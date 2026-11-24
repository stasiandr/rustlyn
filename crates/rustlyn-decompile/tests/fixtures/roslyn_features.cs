using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading.Tasks;

namespace Features
{
    public class Machines
    {
        private int limit = 3;
        private string name;

        public IEnumerable<int> Evens(int[] data, int extra)
        {
            int seen = 0;
            foreach (var d in data)
            {
                if (d % 2 != 0) continue;
                seen++;
                yield return d + extra;
                if (seen >= limit) yield break;
            }
            yield return -1;
        }

        public IEnumerable<string> Lines(string path)
        {
            using (var reader = new StreamReader(path))
            {
                string line;
                while ((line = reader.ReadLine()) != null)
                {
                    try { yield return line; }
                    finally { Console.WriteLine("after"); }
                }
            }
        }

        public async Task<int> SumAsync(Task<int> a, Task<int> b)
        {
            int x = await a;
            if (x > 10) return x;
            int y = await b.ConfigureAwait(false);
            return x + y + limit;
        }

        public async Task RunAsync()
        {
            await Task.Delay(10);
            Console.WriteLine("done");
        }

        public List<int> Query(int[] data, int threshold)
        {
            var big = data.Where(x => x > threshold).Select(x => x * 2).ToList();
            Func<int, int> add = a => a + threshold;
            threshold = 5;
            Console.WriteLine(add(1) + big.Count);
            return big;
        }

        public int Closures(int[] data)
        {
            int count = 0;
            foreach (var d in data)
            {
                Func<int> f = () => d * limit + count;
                count += f();
            }
            int Local(int v) { return v * limit; }
            return count + Local(2);
        }

        public int? Length(Machines other)
        {
            other?.RunAsync();
            name ??= "x";
            return other?.name.Length;
        }
    }
}
