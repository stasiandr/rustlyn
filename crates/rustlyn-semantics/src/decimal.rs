//! `System.Decimal` arithmetic, worked out the way .NET works it out.
//!
//! Roslyn folds a `decimal` constant with the framework's own operators, so
//! the value (and the scale: `1.5m * 2.0m` is `3.00`) an expression has is
//! whatever `System.Decimal` makes of it. A `decimal` is a 96-bit whole
//! number, a scale of 0 to 28 and a sign. An operation is worked out exactly
//! and then rounded to what fits: the fewest digits are dropped that leave 96
//! bits and a scale of at most 28, and a tie goes to the even neighbour.

use std::cmp::Ordering;

/// Why an operation has no value.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum DecimalError {
    /// The answer does not fit a `decimal`.
    Overflow,
    /// A division by zero.
    DivideByZero,
    /// A remainder .NET sometimes refuses with an overflow, in a corner not
    /// worked out; nothing is claimed about it.
    Unsure,
}

/// A `System.Decimal`: its parts, as `GetBits` and `DecimalConstant` give
/// them.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) struct Decimal {
    pub(crate) lo: u32,
    pub(crate) mid: u32,
    pub(crate) hi: u32,
    pub(crate) negative: bool,
    pub(crate) scale: u8,
}

const TWO_96: u128 = 1 << 96;
const MAX_SCALE: u32 = 28;

fn pow10(power: u32) -> u128 {
    10u128.pow(power)
}

/// A number of up to 256 bits, little-endian: what a product or an aligned
/// sum of two `decimal`s is before it is rounded to fit.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Wide([u32; 8]);

impl Wide {
    fn from_u128(value: u128) -> Wide {
        let mut limbs = [0u32; 8];
        for (at, limb) in limbs.iter_mut().take(4).enumerate() {
            *limb = (value >> (32 * at)) as u32;
        }
        Wide(limbs)
    }

    fn product(left: u128, right: u128) -> Wide {
        let a = Wide::from_u128(left).0;
        let b = Wide::from_u128(right).0;
        let mut limbs = [0u32; 8];
        for i in 0..4 {
            let mut carry = 0u64;
            for j in 0..4 {
                if i + j >= 8 {
                    break;
                }
                let cell = u64::from(limbs[i + j]) + u64::from(a[i]) * u64::from(b[j]) + carry;
                limbs[i + j] = cell as u32;
                carry = cell >> 32;
            }
            let mut at = i + 4;
            while carry != 0 && at < 8 {
                let cell = u64::from(limbs[at]) + carry;
                limbs[at] = cell as u32;
                carry = cell >> 32;
                at += 1;
            }
        }
        Wide(limbs)
    }

    fn add(self, other: Wide) -> Wide {
        let mut limbs = [0u32; 8];
        let mut carry = 0u64;
        for (at, limb) in limbs.iter_mut().enumerate() {
            let cell = u64::from(self.0[at]) + u64::from(other.0[at]) + carry;
            *limb = cell as u32;
            carry = cell >> 32;
        }
        Wide(limbs)
    }

    /// `self - other`, where `self` is the larger.
    fn sub(self, other: Wide) -> Wide {
        let mut limbs = [0u32; 8];
        let mut borrow = 0i64;
        for (at, limb) in limbs.iter_mut().enumerate() {
            let mut cell = i64::from(self.0[at]) - i64::from(other.0[at]) - borrow;
            borrow = 0;
            if cell < 0 {
                cell += 1 << 32;
                borrow = 1;
            }
            *limb = cell as u32;
        }
        Wide(limbs)
    }

    fn compare(&self, other: &Wide) -> Ordering {
        for at in (0..8).rev() {
            match self.0[at].cmp(&other.0[at]) {
                Ordering::Equal => {}
                unequal => return unequal,
            }
        }
        Ordering::Equal
    }

    fn is_zero(&self) -> bool {
        self.0.iter().all(|limb| *limb == 0)
    }

    /// Divides by ten in place and returns the remainder.
    fn divide_by_ten(&mut self) -> u32 {
        let mut remainder = 0u64;
        for at in (0..8).rev() {
            let cell = (remainder << 32) | u64::from(self.0[at]);
            self.0[at] = (cell / 10) as u32;
            remainder = cell % 10;
        }
        remainder as u32
    }

    /// The number, where it is below 2^96.
    fn below_two_96(&self) -> Option<u128> {
        if self.0[3..].iter().any(|limb| *limb != 0) {
            return None;
        }
        Some(u128::from(self.0[0]) | u128::from(self.0[1]) << 32 | u128::from(self.0[2]) << 64)
    }

    /// How many bits the number takes.
    fn bits(&self) -> u32 {
        (0..8)
            .rev()
            .find(|at| self.0[*at] != 0)
            .map_or(0, |at| at as u32 * 32 + 32 - self.0[at].leading_zeros())
    }

    fn is_odd(&self) -> bool {
        self.0[0] & 1 != 0
    }
}

impl Decimal {
    pub(crate) const ZERO: Decimal = Decimal {
        lo: 0,
        mid: 0,
        hi: 0,
        negative: false,
        scale: 0,
    };

    /// The parts as a `decimal` holds them, where they are a valid one.
    pub(crate) fn from_parts(
        lo: u32,
        mid: u32,
        hi: u32,
        negative: bool,
        scale: u8,
    ) -> Option<Decimal> {
        (u32::from(scale) <= MAX_SCALE).then_some(Decimal {
            lo,
            mid,
            hi,
            negative,
            scale,
        })
    }

    fn make(magnitude: u128, scale: u32, negative: bool) -> Decimal {
        debug_assert!(magnitude < TWO_96 && scale <= MAX_SCALE);
        Decimal {
            lo: magnitude as u32,
            mid: (magnitude >> 32) as u32,
            hi: (magnitude >> 64) as u32,
            negative,
            scale: scale as u8,
        }
    }

    pub(crate) fn magnitude(&self) -> u128 {
        u128::from(self.hi) << 64 | u128::from(self.mid) << 32 | u128::from(self.lo)
    }

    /// A whole number, which every integer type up to `long` and `ulong`
    /// converts to without loss.
    pub(crate) fn from_integer(value: i128) -> Option<Decimal> {
        let magnitude = value.unsigned_abs();
        (magnitude < TWO_96).then(|| Decimal::make(magnitude, 0, value < 0))
    }

    pub(crate) fn is_zero(&self) -> bool {
        self.magnitude() == 0
    }

    /// The exact value `value / 10^scale`, rounded to fit: the fewest digits
    /// are dropped that leave 96 bits and a scale of at most 28.
    fn fit(value: Wide, scale: u32, negative: bool) -> Result<Decimal, DecimalError> {
        let mut dropped = scale.saturating_sub(MAX_SCALE);
        loop {
            if dropped > scale {
                return Err(DecimalError::Overflow);
            }
            let mut quotient = value;
            let mut last = 0;
            let mut sticky = false;
            for _ in 0..dropped {
                if last != 0 {
                    sticky = true;
                }
                last = quotient.divide_by_ten();
            }
            if dropped > 0 && (last > 5 || (last == 5 && (sticky || quotient.is_odd()))) {
                quotient = quotient.add(Wide::from_u128(1));
            }
            if let Some(magnitude) = quotient.below_two_96() {
                return Ok(Decimal::make(magnitude, scale - dropped, negative));
            }
            dropped += 1;
        }
    }

    pub(crate) fn mul(self, other: Decimal) -> Result<Decimal, DecimalError> {
        let scale = u32::from(self.scale) + u32::from(other.scale);
        // .NET's two ways of multiplying leave a zero differently: with a
        // word above the lowest in either operand a zero product is the plain
        // zero, and with none, a scale 20 above the 28 there is room for
        // rounds everything to the plain zero.
        let wide = (self.hi | self.mid | other.hi | other.mid) != 0;
        let product = Wide::product(self.magnitude(), other.magnitude());
        if (wide && product.is_zero()) || (!wide && scale >= MAX_SCALE + 20) {
            return Ok(Decimal::ZERO);
        }
        Decimal::fit(product, scale, self.negative != other.negative)
    }

    pub(crate) fn add(self, other: Decimal) -> Result<Decimal, DecimalError> {
        self.sum(other, other.negative)
    }

    pub(crate) fn sub(self, other: Decimal) -> Result<Decimal, DecimalError> {
        self.sum(other, !other.negative)
    }

    fn sum(self, other: Decimal, other_negative: bool) -> Result<Decimal, DecimalError> {
        let scale = u32::from(self.scale.max(other.scale));
        let widen = |value: &Decimal| {
            Wide::product(value.magnitude(), pow10(scale - u32::from(value.scale)))
        };
        let (a, b) = (widen(&self), widen(&other));
        // .NET keeps the left operand's sign where the right one does not
        // outweigh it, a zero's included: `-1m + 1m` is `-0`. Two zeros of
        // different scales are the exception: the one with more digits is
        // the answer.
        let (value, negative) = if a.is_zero() && b.is_zero() && self.scale != other.scale {
            (
                a,
                if other.scale > self.scale {
                    other_negative
                } else {
                    self.negative
                },
            )
        } else if self.negative == other_negative {
            (a.add(b), self.negative)
        } else {
            match b.compare(&a) {
                Ordering::Greater => (b.sub(a), other_negative),
                Ordering::Less => (a.sub(b), self.negative),
                // Equal numbers take the sign of the one with fewer digits,
                // and the left one where both have as many.
                Ordering::Equal => (
                    Wide::from_u128(0),
                    if other.scale < self.scale {
                        other_negative
                    } else {
                        self.negative
                    },
                ),
            }
        };
        Decimal::fit(value, scale, negative)
    }

    pub(crate) fn div(self, other: Decimal) -> Result<Decimal, DecimalError> {
        let divisor = other.magnitude();
        if divisor == 0 {
            return Err(DecimalError::DivideByZero);
        }
        let negative = self.negative != other.negative;
        let dividend = self.magnitude();
        let mut scale = i32::from(self.scale) - i32::from(other.scale);
        if dividend == 0 {
            return Ok(Decimal::make(
                0,
                scale.clamp(0, MAX_SCALE as i32) as u32,
                negative,
            ));
        }
        let mut quotient = dividend / divisor;
        let mut remainder = dividend % divisor;
        // A dividend with fewer decimals than the divisor is scaled up to
        // them first: the quotient is a whole number then.
        while scale < 0 {
            let next = remainder * 10;
            quotient = quotient * 10 + next / divisor;
            remainder = next % divisor;
            if quotient >= TWO_96 {
                return Err(DecimalError::Overflow);
            }
            scale += 1;
        }
        if quotient >= TWO_96 {
            return Err(DecimalError::Overflow);
        }
        let mut scale = scale as u32;
        // Digits go on while there is something left over and room for them.
        while remainder != 0 && scale < MAX_SCALE && quotient <= (TWO_96 - 1) / 10 {
            let next = remainder * 10;
            let digit = next / divisor;
            if quotient * 10 + digit >= TWO_96 {
                break;
            }
            quotient = quotient * 10 + digit;
            remainder = next % divisor;
            scale += 1;
        }
        let inexact = remainder != 0;
        let twice = remainder * 2;
        if twice > divisor || (twice == divisor && quotient & 1 != 0) {
            quotient += 1;
        }
        let mut result = Decimal::fit(Wide::from_u128(quotient), scale, negative)?;
        // An answer that had to be cut off loses the zeros the cutting
        // left at its end; an exact one keeps the scale it came to.
        if inexact {
            let mut magnitude = result.magnitude();
            while result.scale > 0 && magnitude % 10 == 0 {
                magnitude /= 10;
                result.scale -= 1;
            }
            result = Decimal::make(magnitude, result.scale.into(), negative);
        }
        Ok(result)
    }

    pub(crate) fn rem(self, other: Decimal) -> Result<Decimal, DecimalError> {
        let divisor = other.magnitude();
        if divisor == 0 {
            return Err(DecimalError::DivideByZero);
        }
        let dividend = self.magnitude();
        if dividend == 0 {
            return Ok(self);
        }
        let scale = u32::from(self.scale.max(other.scale));
        // Both are brought to the larger scale; one of them is as it was.
        let remainder = if self.scale < other.scale {
            // The dividend is scaled up: take the remainder a digit at a time.
            let mut remainder = dividend % divisor;
            for _ in 0..(scale - u32::from(self.scale)) {
                remainder = remainder * 10 % divisor;
            }
            remainder
        } else {
            match divisor.checked_mul(pow10(scale - u32::from(other.scale))) {
                Some(scaled) => dividend % scaled,
                // A divisor too big for 128 bits is bigger than any dividend.
                None => dividend,
            }
        };
        // A remainder is the dividend's own where the dividend is smaller
        // than the divisor (and it keeps its scale there).
        let order = self.compare_magnitude(&other);
        if order == Ordering::Less {
            return Ok(self);
        }
        // .NET sometimes throws an overflow for a dividend with a whole word
        // of ones that has to be scaled past 96 bits, when the quotient has
        // between 32 and 128 bits, and no more is known of when: nothing is
        // claimed there.
        if order == Ordering::Greater
            && [self.lo, self.mid, self.hi].contains(&u32::MAX)
            && self.scale < other.scale
        {
            let scaled = Wide::product(dividend, pow10(scale - u32::from(self.scale)));
            let quotient_bits = scaled.bits() as i32 - (128 - divisor.leading_zeros()) as i32;
            if scaled.below_two_96().is_none() && (30..=129).contains(&quotient_bits) {
                return Err(DecimalError::Unsure);
            }
        }
        Ok(Decimal::make(remainder, scale, self.negative))
    }

    fn compare_magnitude(&self, other: &Decimal) -> Ordering {
        let scale = u32::from(self.scale.max(other.scale));
        let a = Wide::product(self.magnitude(), pow10(scale - u32::from(self.scale)));
        let b = Wide::product(other.magnitude(), pow10(scale - u32::from(other.scale)));
        a.compare(&b)
    }

    /// The order of the two numbers; a zero is a zero whatever its sign.
    pub(crate) fn compare(&self, other: &Decimal) -> Ordering {
        if self.is_zero() && other.is_zero() {
            return Ordering::Equal;
        }
        match (self.negative, other.negative) {
            (false, true) => Ordering::Greater,
            (true, false) => Ordering::Less,
            (false, false) => self.compare_magnitude(other),
            (true, true) => other.compare_magnitude(self),
        }
    }

    /// The whole number a cast to an integer type cuts it to: toward zero.
    pub(crate) fn truncated(&self) -> i128 {
        let whole = (self.magnitude() / pow10(u32::from(self.scale))) as i128;
        if self.negative { -whole } else { whole }
    }

    /// `(double)d`, which .NET works out as the two halves of the number
    /// divided by the power of ten, not as the nearest `double`.
    pub(crate) fn to_f64(self) -> f64 {
        let low = u64::from(self.mid) << 32 | u64::from(self.lo);
        let value = (low as f64 + f64::from(self.hi) * 18_446_744_073_709_551_616.0)
            / double_power(self.scale.into());
        if self.negative { -value } else { value }
    }

    /// `(float)d`.
    pub(crate) fn to_f32(self) -> f32 {
        self.to_f64() as f32
    }

    /// `(decimal)d` for a `double`: the number rounded to 15 significant
    /// digits. `None` where it does not fit a `decimal` (and for a NaN).
    pub(crate) fn from_f64(value: f64) -> Option<Decimal> {
        let bits = value.to_bits();
        let exponent = ((bits >> 52) & 0x7FF) as i32 - 1022;
        Decimal::from_floating(value.abs(), exponent, value.is_sign_negative(), 15)
    }

    /// `(decimal)f` for a `float`: the number rounded to 7 significant
    /// digits.
    pub(crate) fn from_f32(value: f32) -> Option<Decimal> {
        let bits = value.to_bits();
        let exponent = ((bits >> 23) & 0xFF) as i32 - 126;
        Decimal::from_floating(
            f64::from(value).abs(),
            exponent,
            value.is_sign_negative(),
            7,
        )
    }

    fn from_floating(
        magnitude: f64,
        exponent: i32,
        negative: bool,
        digits: i32,
    ) -> Option<Decimal> {
        // Anything under 2^-94 is nothing a scale of 28 can show.
        if exponent < -94 {
            return Some(Decimal::ZERO);
        }
        if exponent > 96 {
            return None;
        }
        let mut dbl = magnitude;
        let mut power = digits - 1 - ((exponent * 19728) >> 16);
        if power >= 0 {
            power = power.min(MAX_SCALE as i32);
            dbl *= double_power(power as u32);
        } else if power != -1 || dbl >= 10f64.powi(digits) {
            dbl /= double_power((-power) as u32);
        } else {
            power = 0;
        }
        if dbl < 10f64.powi(digits - 1) && power < MAX_SCALE as i32 {
            dbl *= 10.0;
            power += 1;
        }
        let mut mantissa = dbl as u64;
        let fraction = dbl - mantissa as f64;
        if fraction > 0.5 || (fraction == 0.5 && mantissa & 1 != 0) {
            mantissa += 1;
        }
        if mantissa == 0 {
            return Some(Decimal::ZERO);
        }
        let mut mantissa = u128::from(mantissa);
        if power < 0 {
            mantissa *= pow10((-power) as u32);
            power = 0;
        } else {
            let mut removable = power.min(digits - 1);
            while removable > 0 && mantissa % 10 == 0 {
                mantissa /= 10;
                power -= 1;
                removable -= 1;
            }
        }
        (mantissa < TWO_96).then(|| Decimal::make(mantissa, power as u32, negative))
    }

    /// The number as C# writes it: `1.50`.
    pub(crate) fn text(&self) -> String {
        let mut digits = self.magnitude().to_string();
        let scale = usize::from(self.scale);
        if scale > 0 {
            while digits.len() <= scale {
                digits.insert(0, '0');
            }
            digits.insert(digits.len() - scale, '.');
        }
        if self.negative && !self.is_zero() {
            digits.insert(0, '-');
        }
        digits
    }
}

/// `10^power` as a `double`: the nearest one the language writes as `1e<power>`.
fn double_power(power: u32) -> f64 {
    const POWERS: [f64; 29] = [
        1e0, 1e1, 1e2, 1e3, 1e4, 1e5, 1e6, 1e7, 1e8, 1e9, 1e10, 1e11, 1e12, 1e13, 1e14, 1e15, 1e16,
        1e17, 1e18, 1e19, 1e20, 1e21, 1e22, 1e23, 1e24, 1e25, 1e26, 1e27, 1e28,
    ];
    POWERS[power as usize]
}

#[cfg(test)]
mod tests {
    use super::*;

    /// What `System.Decimal` made of each operation, one per line as `op
    /// operands... result`, each number written as the `lo,mid,hi,flags` of
    /// `decimal.GetBits`: sampled from a few hundred thousand worked out by
    /// the framework (add, sub, mul, div, rem, and the conversions).
    const FRAMEWORK: &str = "\
add 2444312998,1532173217,327022997,262144 3783029985,2299740339,1,2149253120 2968293500,2436830287,3270229973,327680
add 4294967295,4294967295,4294967295,524288 4294967295,4294967295,4294967295,524288 858993459,858993459,858993459,458752
add 3343828338,3716765592,3357372941,655360 0,0,0,2148204544 3343828338,3716765592,3357372941,655360
add 27,0,0,1048576 84,0,0,2147680256 3181150181,195577,0,2148532224
add 220479167,9745551,0,0 3779578018,522360572,0,2149318656 3775328032,188172860,2269062924,786432
sub 2576980377,2576980377,429496729,851968 742537922,0,0,720896 1337632209,2576980360,429496729,851968
sub 3421317055,859065697,0,1769472 216914,0,0,2147680256 1016575789,999031838,1175893150,1703936
sub 29,0,0,0 926573510,1117626649,429496731,65536 926573220,1117626649,429496731,2147549184
sub 3418269213,1330866725,4124066876,2149056512 3418269213,1330866725,4124066876,1572864 1542647302,1125166804,824813375,2148990976
sub 1087649948,1750458344,437110218,524288 1087649948,1750458344,437110218,2148007936 2175299896,3500916688,874220436,524288
mul 1615495272,2769174448,1,2148532224 3453151744,2874214728,1644748,2148925440 3558450955,3635154187,499020985,1376256
mul 3832774299,0,0,1310720 93,0,0,458752 4260691535,82,0,1769472
mul 3770868987,1091955426,2572370262,2149056512 3770868987,1091955426,2572370262,1572864 2861812178,3514044434,1220637429,2148728832
mul 0,0,1,0 5,0,0,65536 0,0,5,65536
mul 86,0,0,2147549184 3555040145,3224040990,2242134572,393216 1854743682,2429077868,1928235732,2147811328
div 708,0,0,0 282022162,1846122956,429496729,2147549184 8936,0,0,2149318656
div 663116644,0,0,2147483648 1938632053,10839,0,786432 2680963938,3375412207,772152431,2148859904
div 756968292,1061492127,2021580516,131072 1364187018,2683129590,202158051,2147549184 10,0,0,2147549184
div 2576980377,2576980377,429496729,262144 2116575949,3062378026,4293711384,2149318656 1283583542,3864331169,542259650,2147811328
div 1126968949,2832021559,1205631575,917504 1126968949,2832021559,1205631575,917504 1,0,0,0
rem 3663221488,6,0,262144 458249148,10,0,2148532224 4135612788,9,0,1048576
rem 2,0,0,0 276447232,23283,0,0 2,0,0,0
rem 510871,0,0,131072 2649221908,533960261,436764726,2147549184 510871,0,0,131072
rem 2334024643,2398577929,29970,2147680256 892579955,0,0,2148663296 262624235,0,0,2148663296
rem 29,0,0,2148859904 3118277378,3896669440,3445457676,1703936 29,0,0,2148859904
mul 3746623218,3845208704,1888154972,0 2441894314,1168103390,2,2148270080 OVF
mul 2178987108,3954759252,0,851968 1919453212,577132843,2564758084,0 OVF
div 3792905859,872150111,96546,2147811328 1988,0,0,2149253120 OVF
div 428896558,1194072537,1995872150,65536 0,0,0,2148007936 DIV
rem 2827108410,2349019590,771704436,1769472 0,0,0,2148401152 DIV
add 636653774,3841078686,436500646,2148401152 636653774,3841078686,436500646,917504 0,0,0,2148401152
add 638717725,589376080,3745108551,917504 638717725,589376080,3745108551,2148401152 0,0,0,917504
add 3618493798,3360891870,3158489966,1638400 3618493798,3360891870,3158489966,2149122048 0,0,0,1638400
add 6,0,0,524288 6,0,0,2148007936 0,0,0,524288
mul 0,0,0,0 0,0,0,2148335616 0,0,0,2148335616
mul 0,0,0,2149318656 0,0,0,0 0,0,0,2149318656
mul 3699968933,3739400031,4160773361,2149318656 0,0,0,2149187584 0,0,0,0
mul 0,0,0,1179648 2530257067,460416488,2340036305,2148794368 0,0,0,0
rem 2576980378,2576980377,429496729,1179648 2576980378,2576980377,429496729,2148663296 0,0,0,1179648
rem 0,0,0,2149056512 3762608245,2764045704,3446864793,2148270080 0,0,0,2149056512
div 893,0,0,0 738632059,232497590,429496731,131072 112712,0,0,1835008
mul 283111616,2498355048,20833790,1835008 882,0,0,2147614720 3184239220,3996628880,183754032,2149318656
mul 1859607735,1316088089,0,2148728832 3795740160,4156973409,306425636,2149318656 3903778936,3928750419,173208785,1835008
mul 2582,0,0,2148073472 1065866322,7914182,0,1179648 3287773964,3254549380,4,2149253120
div 20,0,0,0 3034310767,3913746222,429496733,2147483648 25,0,0,2149318656
div 4294967295,4294967295,4294967295,2148990976 3354641166,1225608446,0,917504 2030793516,2821972756,815921269,2149253120
f64 3022261592,0,0,1376256 4434521190973059920
f64 30,0,0,2148270080 -4773676929492776080
f64 425344336,0,0,1310720 4436807541172744604
f32 40,0,0,2148335616 -1400062772
f32 2243710624,3404411810,2353919789,1835008 1082848110
f32 0,0,0,2147614720 -2147483648
trn 32,0,0,1572864 0
trn 2021564912,0,0,2147549184 -202156491
trn 985461,0,0,393216 0
d2m 4477061044614909757 1512872294,48019,0,1507328
d2m -4702407661594321672 3848876048,41205,0,2148794368
d2m -4979411422384298305 5578,0,0,2149318656
d2m -5023520422417245651 6,0,0,2149318656
d2m 4464797317639690289 1169758325,75035,0,1572864
d2m -4971973988617027584 16544,0,0,2149318656
d2m 9125185150043526805 OVF
d2m 8389587253801881143 OVF
f2m 436207616 264698,0,0,1835008
f2m -974006477 77389,0,0,2147549184
f2m -1050673152 14,0,0,2147483648
f2m 723073155 5443495,0,0,1245184
f2m 1136852627 3899889,0,0,262144
cmp 151072451,1352839058,46407769,2148139008 1510724510,643488692,464077693,2148204544 0
cmp 4171898854,3134790504,0,2148728832 4171898854,3134790504,0,1245184 -1
cmp 704,0,0,0 3280436250,3701271063,429496721,2147483648 1
";

    fn parse(bits: &str) -> Decimal {
        let words: Vec<u32> = bits.split(',').map(|word| word.parse().unwrap()).collect();
        Decimal {
            lo: words[0],
            mid: words[1],
            hi: words[2],
            negative: words[3] & 0x8000_0000 != 0,
            scale: (words[3] >> 16) as u8,
        }
    }

    fn show(result: Result<Decimal, DecimalError>) -> String {
        match result {
            Ok(value) => format!(
                "{},{},{},{}",
                value.lo,
                value.mid,
                value.hi,
                u32::from(value.scale) << 16 | if value.negative { 0x8000_0000 } else { 0 }
            ),
            Err(DecimalError::Overflow) => "OVF".into(),
            Err(DecimalError::DivideByZero) => "DIV".into(),
            Err(DecimalError::Unsure) => "UNSURE".into(),
        }
    }

    #[test]
    fn every_operation_gives_what_the_framework_gave() {
        let mut worked = 0;
        for line in FRAMEWORK.lines() {
            let parts: Vec<&str> = line.split(' ').collect();
            let op = parts[0];
            let expected = *parts.last().unwrap();
            let got = match op {
                "add" | "sub" | "mul" | "div" | "rem" => {
                    let (a, b) = (parse(parts[1]), parse(parts[2]));
                    show(match op {
                        "add" => a.add(b),
                        "sub" => a.sub(b),
                        "mul" => a.mul(b),
                        "div" => a.div(b),
                        _ => a.rem(b),
                    })
                }
                "cmp" => (parse(parts[1]).compare(&parse(parts[2])) as i32).to_string(),
                "f64" => (parse(parts[1]).to_f64().to_bits() as i64).to_string(),
                "f32" => (parse(parts[1]).to_f32().to_bits() as i32).to_string(),
                "trn" => parse(parts[1]).truncated().to_string(),
                "d2m" => show(
                    Decimal::from_f64(f64::from_bits(parts[1].parse::<i64>().unwrap() as u64))
                        .ok_or(DecimalError::Overflow),
                ),
                "f2m" => show(
                    Decimal::from_f32(f32::from_bits(parts[1].parse::<i32>().unwrap() as u32))
                        .ok_or(DecimalError::Overflow),
                ),
                other => panic!("an operation named {other}"),
            };
            assert_eq!(got, expected, "{line}");
            worked += 1;
        }
        assert!(worked > 50);
    }

    fn dec(text: &str) -> Decimal {
        let negative = text.starts_with('-');
        let text = text.trim_start_matches('-');
        let scale = text.find('.').map_or(0, |at| text.len() - at - 1);
        let digits: String = text.chars().filter(|c| *c != '.').collect();
        let magnitude: u128 = digits.parse().unwrap();
        Decimal::from_parts(
            magnitude as u32,
            (magnitude >> 32) as u32,
            (magnitude >> 64) as u32,
            negative,
            scale as u8,
        )
        .unwrap()
    }

    #[test]
    fn a_quotient_is_rounded_to_what_fits_and_cut_of_its_zeros() {
        let text = |result: Result<Decimal, DecimalError>| result.unwrap().text();
        assert_eq!(
            text(dec("1").div(dec("3"))),
            "0.3333333333333333333333333333"
        );
        assert_eq!(
            text(dec("2").div(dec("3"))),
            "0.6666666666666666666666666667"
        );
        assert_eq!(
            text(dec("100").div(dec("3"))),
            "33.333333333333333333333333333"
        );
        assert_eq!(text(dec("10").div(dec("4"))), "2.5");
        assert_eq!(text(dec("1.50").div(dec("0.5"))), "3.0");
    }

    #[test]
    fn a_product_keeps_the_digits_the_operands_had() {
        let text = |result: Result<Decimal, DecimalError>| result.unwrap().text();
        assert_eq!(text(dec("1.5").mul(dec("2.0"))), "3.00");
        assert_eq!(text(dec("1.50").add(dec("0.5"))), "2.00");
        assert_eq!(text(dec("5.5").rem(dec("2"))), "1.5");
        assert_eq!(text(dec("-7").rem(dec("3"))), "-1");
    }

    #[test]
    fn what_does_not_fit_is_an_overflow_or_a_division_by_zero() {
        let max = dec("79228162514264337593543950335");
        assert_eq!(max.mul(dec("2")), Err(DecimalError::Overflow));
        assert_eq!(max.add(dec("1")), Err(DecimalError::Overflow));
        assert_eq!(dec("1").div(dec("0")), Err(DecimalError::DivideByZero));
        assert_eq!(dec("5").rem(dec("0.0")), Err(DecimalError::DivideByZero));
        assert_eq!(Decimal::from_f64(1e40), None);
        assert_eq!(Decimal::from_f64(f64::NAN), None);
        assert_eq!(Decimal::from_f64(1e-30), Some(Decimal::ZERO));
    }

    #[test]
    fn a_double_is_rounded_to_fifteen_digits_and_a_float_to_seven() {
        let text = |value: Option<Decimal>| value.unwrap().text();
        assert_eq!(text(Decimal::from_f64(3.5)), "3.5");
        assert_eq!(text(Decimal::from_f64(0.1)), "0.1");
        assert_eq!(
            text(Decimal::from_f64(1.234_567_890_123_456_7e20)),
            "123456789012346000000"
        );
        assert_eq!(text(Decimal::from_f32(0.1)), "0.1");
        assert_eq!(text(Decimal::from_f32(1.1)), "1.1");
    }

    #[test]
    fn a_zero_keeps_its_sign_and_scale_as_the_framework_gives_them() {
        let minus_zero = dec("-0");
        assert!(dec("1").mul(minus_zero).unwrap().negative);
        assert!(dec("-1").add(dec("1")).unwrap().negative);
        // Equal numbers take the sign of the one with fewer digits.
        let zero = dec("1.0").sub(dec("1")).unwrap();
        assert_eq!((zero.scale, zero.negative), (1, true));
        let zero = dec("1").sub(dec("1.0")).unwrap();
        assert_eq!((zero.scale, zero.negative), (1, false));
        assert_eq!(minus_zero.to_f64().to_bits(), (-0.0f64).to_bits());
    }
}
