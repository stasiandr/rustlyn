using System; using System.Threading; using System.Threading.Tasks; using Polly; using Polly.Retry;
class Program { static async Task Main() {
    int attempts = 0;
    var pipeline = new ResiliencePipelineBuilder().AddRetry(new RetryStrategyOptions { MaxRetryAttempts = 3, Delay = TimeSpan.Zero, OnRetry = a => { Console.WriteLine("retry " + a.AttemptNumber); return default; } }).Build();
    var result = await pipeline.ExecuteAsync(async ct => { attempts++; await Task.Yield(); if (attempts < 3) throw new InvalidOperationException("flaky"); return "ok after " + attempts; }, CancellationToken.None);
    Console.WriteLine(result);
    var sync = pipeline.Execute(() => 42);
    Console.WriteLine(sync);
} }
