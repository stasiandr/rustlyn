using System;
using System.Collections.Generic;

namespace Game
{
    enum Kind { Melee, Ranged, Magic }

    class Weapon
    {
        public string Name { get; set; }
        public int Damage;
    }

    class Player
    {
        private int health = 100;
        private readonly string _name;
        public int Level { get; private set; }
        public Kind Kind { get; set; }

        public Player(string name, int level)
        {
            _name = name;
            Level = level;
        }

        public int Health
        {
            get { return health; }
            set { health = value; }
        }

        public string Describe(int bonus)
        {
            int total = Level * 2 + bonus;
            string label = "Player " + _name + " has " + total + " points";
            if (total > 10 && bonus != 0)
            {
                Console.WriteLine(label);
            }
            else
            {
                Console.WriteLine("weak");
            }
            return label;
        }

        public int Score(int[] values)
        {
            int sum = 0;
            for (int i = 0; i < values.Length; i++)
            {
                sum += values[i];
            }
            foreach (var value in values)
                Console.WriteLine(value);
            return sum;
        }

        public string Title(int rank)
        {
            switch (rank)
            {
                case 1:
                    return "gold";
                case 2:
                case 3:
                    return "silver";
                default:
                    return "none";
            }
        }

        public string Name(Kind kind)
        {
            if (kind == Kind.Melee)
                return "sword";
            else if (kind == Kind.Ranged)
                return "bow";
            else
                return "staff";
        }

        public int Pick(bool first, int a, int b)
        {
            if (first)
            {
                return a;
            }
            return b;
        }

        public void Heal(int amount)
        {
            if (amount > 0)
            {
                health = health + amount;
                Console.WriteLine(health);
            }
        }

        public int Twice(int x) => x * 2;

        public Weapon Arm(string name)
        {
            var weapon = new Weapon();
            weapon.Name = name;
            weapon.Damage = Level * 3;
            List<int> hits = new List<int>();
            hits.Add(1);
            hits.Add(2);
            Func<int, int> square = n => n * n;
            int Local(int y)
            {
                return y + square(y);
            }
            Console.WriteLine(Local(hits.Count));
            return weapon;
        }

        public bool Check(string text, object other)
        {
            var length = text.Length;
            bool empty = length == 0 || other is null;
            return empty ? false : length > 3;
        }
    }
}
