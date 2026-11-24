using System; using Serilog; using Serilog.Core; using Serilog.Events;
class ConsoleSink : ILogEventSink { public void Emit(LogEvent e) { Console.WriteLine($"[{e.Level}] {e.RenderMessage()}"); } }
class Program { static void Main() {
    var log = new LoggerConfiguration().MinimumLevel.Debug().WriteTo.Sink(new ConsoleSink()).Enrich.WithProperty("App", "demo").CreateLogger();
    log.Information("Hello {Name}, you are {Age} years old", "Ada", 36);
    log.Warning("Items: {@Items}", new[] { 1, 2, 3 });
    log.ForContext<Program>().Debug("ctx {Pos}", new { X = 1, Y = 2 });
    try { throw new InvalidOperationException("boom"); } catch (Exception ex) { log.Error(ex, "failed {Op}", "op"); }
} }
