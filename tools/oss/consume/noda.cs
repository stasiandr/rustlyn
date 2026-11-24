using System; using NodaTime; using NodaTime.Text;
class Program { static void Main() {
    var d = new LocalDate(2024, 2, 28).PlusDays(2);
    Console.WriteLine(d + " " + d.DayOfWeek + " " + d.Era);
    var p = Period.Between(new LocalDate(2000, 1, 1), d, PeriodUnits.YearMonthDay);
    Console.WriteLine(p);
    var i = Instant.FromUtc(2024, 3, 1, 12, 30);
    Console.WriteLine(InstantPattern.General.Format(i));
    var zone = DateTimeZone.ForOffset(Offset.FromHours(2));
    Console.WriteLine(i.InZone(zone).LocalDateTime);
    Console.WriteLine(LocalDatePattern.Iso.Parse("2025-12-31").Value.PlusMonths(1));
} }
