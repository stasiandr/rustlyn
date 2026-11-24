// What the .NET Regex source generator writes for the two [GeneratedRegex]
// partials in AnalyzerConfig.cs. Roslyn's own build gets these from the
// generator; a compiler run without generators has to be given them, and both
// compilers under test are given the same file.
#nullable enable
using System.Text.RegularExpressions;

namespace Microsoft.CodeAnalysis
{
    public sealed partial class AnalyzerConfig
    {
        private static partial Regex GetSectionMatcherRegex()
            => new Regex(@"^\s*\[(([^#;]|\\#|\;)+)\]\s*([#;].*)?$", RegexOptions.Compiled);

        private static partial Regex GetPropertyMatcherRegex()
            => new Regex(@"^\s*([\w\.\-_]+)\s*[=:]\s*(.*?)\s*([#;].*)?$", RegexOptions.Compiled);
    }
}
