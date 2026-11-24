using System; using FluentValidation;
class Customer { public string Name { get; set; } public int Age { get; set; } public string Email { get; set; } }
class CustomerValidator : AbstractValidator<Customer> { public CustomerValidator() {
    RuleFor(c => c.Name).NotEmpty().MinimumLength(3);
    RuleFor(c => c.Age).InclusiveBetween(18, 120);
    RuleFor(c => c.Email).EmailAddress().When(c => c.Email != null);
} }
class Program { static void Main() {
    var v = new CustomerValidator();
    var r = v.ValidateAsync(new Customer { Name = "Al", Age = 7, Email = "nope" }).GetAwaiter().GetResult();
    Console.WriteLine(r.IsValid);
    foreach (var e in r.Errors) Console.WriteLine(e.PropertyName + ": " + e.ErrorMessage);
    Console.WriteLine(v.ValidateAsync(new Customer { Name = "Alice", Age = 30, Email = "a@b.co" }).GetAwaiter().GetResult().IsValid);
} }
