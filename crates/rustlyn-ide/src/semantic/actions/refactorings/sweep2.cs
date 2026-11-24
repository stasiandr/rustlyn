using System;
using System.Collections.Generic;

namespace Tools;

static class Text
{
    public static int Twice(this string s) => s.Length * 2;
}

sealed class Resource : IDisposable
{
    public void Dispose() { }
}

class Inventory<T> where T : class
{
    private readonly List<T> items = new List<T>();
    private int version;
    public int Count => items.Count;
    public string Path = @"C:\data\items";

    public T First(Func<T, bool> test)
    {
        for (int i = 0; i < items.Count; i++)
        {
            if (test(items[i]))
            {
                return items[i];
            }
        }
        return null;
    }

    public void Add(T item, bool log)
    {
        if (item == null) throw new ArgumentNullException("item");
        items.Add(item);
        version++;
        if (log)
            Console.WriteLine("added " + version);
    }

    public int Parse(string text)
    {
        int result;
        if (int.TryParse(text, out var parsed))
        {
            result = parsed;
        }
        else
        {
            result = -1;
        }
        return result;
    }

    public int Size(int? maybe, object o)
    {
        int size = maybe ?? 0;
        if (o is string s && s.Length > 0)
        {
            size = size + s.Twice();
        }
        while (size > 100)
        {
            size = size / 2;
        }
        do
        {
            size--;
        } while (size > 50);
        using (var resource = new Resource())
        {
            Console.WriteLine(size);
        }
        return size;
    }

    public string Grade(int score)
    {
        string grade;
        switch (score / 10)
        {
            case 10:
            case 9:
                grade = "A";
                break;
            case 8:
                grade = "B";
                break;
            default:
                grade = "F";
                break;
        }
        return grade;
    }

    public double Area(double radius)
    {
        const double half = 0.5;
        double area = 3.14159 * radius * radius;
        Func<double, double> scale = x =>
        {
            return x * half;
        };
        return scale(area);
    }

    public static int Sum(List<int> values)
    {
        int total = 0;
        foreach (int value in values)
        {
            total += value;
        }
        return total > 0 ? total : 0;
    }
}
