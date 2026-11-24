// What hot patches lean on at run time: storage for the fields an edit adds
// to a class the editor has already loaded. A loaded type cannot grow a
// field, so a patch keeps the new one beside each instance, in a table the
// garbage collector clears with the instance. Statics are kept by name.
// A field with a first value — an initializer, or what the constructor that
// objects made before the patch never ran would have given it — takes it
// when it is first read.
using System.Collections.Generic;
using System.Runtime.CompilerServices;

namespace PilotRuntime
{
    public static class Fields
    {
        sealed class Box<T>
        {
            public T Value;
        }

        static readonly ConditionalWeakTable<object, Dictionary<string, object>> instances =
            new ConditionalWeakTable<object, Dictionary<string, object>>();

        static readonly Dictionary<string, object> statics = new Dictionary<string, object>();

        /// The field `key` of `owner`, created with its type's default value.
        public static ref T Of<T>(object owner, string key)
        {
            var fields = instances.GetValue(owner, _ => new Dictionary<string, object>());
            if (!fields.TryGetValue(key, out var box))
            {
                box = new Box<T>();
                fields[key] = box;
            }
            return ref ((Box<T>)box).Value;
        }

        /// The field `key` of `owner`, first `first(owner)`.
        public static ref T Of<T>(object owner, string key, System.Func<object, T> first)
        {
            var fields = instances.GetValue(owner, _ => new Dictionary<string, object>());
            if (!fields.TryGetValue(key, out var box))
            {
                box = new Box<T> { Value = first(owner) };
                fields[key] = box;
            }
            return ref ((Box<T>)box).Value;
        }

        /// The static field `key`, first `first()`.
        public static ref T Static<T>(string key, System.Func<T> first)
        {
            if (!statics.TryGetValue(key, out var box))
            {
                box = new Box<T> { Value = first() };
                statics[key] = box;
            }
            return ref ((Box<T>)box).Value;
        }

        /// What the field `name` the loaded type declares holds on `owner`,
        /// as a `T`: the first value of a serialized field an edit gave
        /// another type, which Unity still fills in the old one. A component
        /// comes from a game object, a game object from a component, a number
        /// from a number; anything else starts empty.
        public static T Former<T>(object owner, string name)
        {
            const System.Reflection.BindingFlags flags = System.Reflection.BindingFlags.Instance
                | System.Reflection.BindingFlags.Public | System.Reflection.BindingFlags.NonPublic
                | System.Reflection.BindingFlags.DeclaredOnly;
            System.Reflection.FieldInfo field = null;
            for (var type = owner.GetType(); type != null && field == null; type = type.BaseType)
                field = type.GetField(name, flags);
            var value = field?.GetValue(owner);
            if (value == null) return default;
            if (value is T same) return same;
            var target = typeof(T);
            var component = typeof(UnityEngine.Component).IsAssignableFrom(target);
            UnityEngine.Object found = null;
            if (value is UnityEngine.GameObject gameObject && component)
                found = gameObject.GetComponent(target);
            else if (value is UnityEngine.Component held && target == typeof(UnityEngine.GameObject))
                found = held.gameObject;
            else if (value is UnityEngine.Component other && component)
                found = other.GetComponent(target);
            else if (value is System.IConvertible && typeof(System.IConvertible).IsAssignableFrom(target))
                return (T)System.Convert.ChangeType(value, target);
            return found == null ? default : (T)(object)found;
        }

        /// `owner?.Added`, for a field an edit added: what `get` reads where
        /// there is an owner.
        public static TValue Through<TOwner, TValue>(TOwner owner, System.Func<TOwner, TValue> get)
            where TOwner : class where TValue : class =>
            owner == null ? null : get(owner);

        /// The same for a field of a value type, which reads as nullable.
        public static TValue? ThroughValue<TOwner, TValue>(TOwner owner, System.Func<TOwner, TValue> get)
            where TOwner : class where TValue : struct =>
            owner == null ? (TValue?)null : get(owner);

        /// The static field `key`.
        public static ref T Static<T>(string key)
        {
            if (!statics.TryGetValue(key, out var box))
            {
                box = new Box<T>();
                statics[key] = box;
            }
            return ref ((Box<T>)box).Value;
        }
    }

    /// Sets what `value` has to be set through a reference.
    public delegate void Setter<T>(ref T value);

    /// An object initializer that names fields an edit added: the object is
    /// made with what the loaded type has, then given the rest.
    public static class Init
    {
        public static T With<T>(T value, Setter<T> set)
        {
            set(ref value);
            return value;
        }
    }

    /// An object made with none of its constructors run, for a patch's
    /// constructor to make what it is.
    public static class Make
    {
        public static T Blank<T>() where T : class =>
            (T)System.Runtime.Serialization.FormatterServices.GetUninitializedObject(typeof(T));
    }

    /// What a hot patch calls a base implementation through: a member
    /// called on `Base.Of<T>(instance)` is called as `T` implements it, not
    /// as the instance's own type overrides it — Rustlyn makes that call
    /// directly, as `base.M()` would be.
    public static class Base
    {
        public static T Of<T>(object instance) where T : class => (T)instance;
    }

    /// What a hot patch reaches a `protected` member of a class from another
    /// assembly through: the patch is no subclass, and the runtime would
    /// refuse it the call. A method made here at run time, told to skip
    /// that check, makes the call for it — `call` for `base.M()`, `callvirt`
    /// otherwise — and is kept for the next time.
    public static class Protected
    {
        static readonly Dictionary<string, System.Delegate> made = new Dictionary<string, System.Delegate>();

        const System.Reflection.BindingFlags All = System.Reflection.BindingFlags.Public
            | System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Instance
            | System.Reflection.BindingFlags.Static;

        public static TDelegate Call<TDelegate>(System.Type owner, string name, System.Type[] parameters, bool virtualCall)
            where TDelegate : class
        {
            var key = $"{owner.AssemblyQualifiedName}|{name}|{string.Join(",", System.Array.ConvertAll(parameters, type => type.AssemblyQualifiedName))}|{virtualCall}|{typeof(TDelegate).AssemblyQualifiedName}";
            lock (made)
            {
                if (made.TryGetValue(key, out var kept)) return (TDelegate)(object)kept;
                var method = owner.GetMethod(name, All, null, parameters, null)
                    ?? throw new System.MissingMethodException(owner.FullName, name);
                var created = Make<TDelegate>(name, il =>
                {
                    var count = parameters.Length + (method.IsStatic ? 0 : 1);
                    for (var index = 0; index < count; index++) il.Emit(System.Reflection.Emit.OpCodes.Ldarg, (short)index);
                    il.Emit(virtualCall && method.IsVirtual ? System.Reflection.Emit.OpCodes.Callvirt : System.Reflection.Emit.OpCodes.Call, method);
                    il.Emit(System.Reflection.Emit.OpCodes.Ret);
                }, owner);
                made[key] = created;
                return (TDelegate)(object)created;
            }
        }

        public static TDelegate Field<TDelegate>(System.Type owner, string name) where TDelegate : class
        {
            var key = $"{owner.AssemblyQualifiedName}|{name}|field|{typeof(TDelegate).AssemblyQualifiedName}";
            lock (made)
            {
                if (made.TryGetValue(key, out var kept)) return (TDelegate)(object)kept;
                var field = owner.GetField(name, All) ?? throw new System.MissingFieldException(owner.FullName, name);
                var created = Make<TDelegate>(name, il =>
                {
                    if (field.IsStatic)
                        il.Emit(System.Reflection.Emit.OpCodes.Ldsfld, field);
                    else
                    {
                        il.Emit(System.Reflection.Emit.OpCodes.Ldarg_0);
                        il.Emit(System.Reflection.Emit.OpCodes.Ldfld, field);
                    }
                    il.Emit(System.Reflection.Emit.OpCodes.Ret);
                }, owner);
                made[key] = created;
                return (TDelegate)(object)created;
            }
        }

        /// A constructor of `owner` called on an object that is already there:
        /// what a patched constructor chains to.
        public static TDelegate Constructor<TDelegate>(System.Type owner, System.Type[] parameters) where TDelegate : class
        {
            var key = $"{owner.AssemblyQualifiedName}|.ctor|{string.Join(",", System.Array.ConvertAll(parameters, type => type.AssemblyQualifiedName))}|{typeof(TDelegate).AssemblyQualifiedName}";
            lock (made)
            {
                if (made.TryGetValue(key, out var kept)) return (TDelegate)(object)kept;
                var constructor = owner.GetConstructor(All, null, parameters, null)
                    ?? throw new System.MissingMethodException(owner.FullName, ".ctor");
                var created = Make<TDelegate>("ctor", il =>
                {
                    for (var index = 0; index <= parameters.Length; index++) il.Emit(System.Reflection.Emit.OpCodes.Ldarg, (short)index);
                    il.Emit(System.Reflection.Emit.OpCodes.Call, constructor);
                    il.Emit(System.Reflection.Emit.OpCodes.Ret);
                }, owner);
                made[key] = created;
                return (TDelegate)(object)created;
            }
        }

        public static TDelegate SetField<TDelegate>(System.Type owner, string name) where TDelegate : class
        {
            var key = $"{owner.AssemblyQualifiedName}|{name}|set field|{typeof(TDelegate).AssemblyQualifiedName}";
            lock (made)
            {
                if (made.TryGetValue(key, out var kept)) return (TDelegate)(object)kept;
                var field = owner.GetField(name, All) ?? throw new System.MissingFieldException(owner.FullName, name);
                var created = Make<TDelegate>(name, il =>
                {
                    il.Emit(System.Reflection.Emit.OpCodes.Ldarg_0);
                    if (field.IsStatic)
                        il.Emit(System.Reflection.Emit.OpCodes.Stsfld, field);
                    else
                    {
                        il.Emit(System.Reflection.Emit.OpCodes.Ldarg_1);
                        il.Emit(System.Reflection.Emit.OpCodes.Stfld, field);
                    }
                    il.Emit(System.Reflection.Emit.OpCodes.Ret);
                }, owner);
                made[key] = created;
                return (TDelegate)(object)created;
            }
        }

        static System.Delegate Make<TDelegate>(string name, System.Action<System.Reflection.Emit.ILGenerator> body, System.Type owner)
        {
            var invoke = typeof(TDelegate).GetMethod("Invoke");
            var parameters = System.Array.ConvertAll(invoke.GetParameters(), parameter => parameter.ParameterType);
            var method = new System.Reflection.Emit.DynamicMethod("PilotProtected_" + name, invoke.ReturnType, parameters, owner.Module, true);
            body(method.GetILGenerator());
            return method.CreateDelegate(typeof(TDelegate));
        }
    }
}
