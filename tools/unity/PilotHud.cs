// What the watcher (`hot.py`) did with each save, shown in the editor: a
// notification over every Scene and Game view, and a window of its own
// (Window > Pilot Hot Reload) with the last change — what it patched, how
// long it took, the lines that changed — and the ones before it. With Pilot
// beside Unity, a save in one says in the other what it changed.
//
// The watcher appends one JSON object per event to Temp/PilotProbe/hud.jsonl;
// a file outlives the domain reloads it reports.
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using UnityEditor;
using UnityEngine;
using UnityEngine.UIElements;

[Serializable]
public class PilotEvent
{
    public string time;
    // patch, same, broken, reload, deleted, failed, info
    public string kind;
    public string file;
    public string title;
    public string detail;
    public float seconds;
    public string[] diff;
}

[InitializeOnLoad]
public static class PilotHud
{
    public static readonly string Path = "Temp/PilotProbe/hud.jsonl";
    public static readonly List<PilotEvent> Events = new List<PilotEvent>();
    public static event Action Changed;
    static long read;
    static double polled;

    static PilotHud()
    {
        // What was there before this domain was loaded is history, not news.
        Load(notify: false);
        EditorApplication.update += Poll;
    }

    static void Poll()
    {
        if (EditorApplication.timeSinceStartup - polled < 0.1) return;
        polled = EditorApplication.timeSinceStartup;
        Load(notify: true);
    }

    static void Load(bool notify)
    {
        if (!File.Exists(Path)) return;
        var length = new FileInfo(Path).Length;
        if (length < read) { Events.Clear(); read = 0; }
        if (length == read) return;
        string text;
        using (var stream = new FileStream(Path, FileMode.Open, FileAccess.Read, FileShare.ReadWrite))
        {
            stream.Seek(read, SeekOrigin.Begin);
            text = new StreamReader(stream).ReadToEnd();
        }
        // A line not yet ended is read next time.
        var end = text.LastIndexOf('\n');
        if (end < 0) return;
        read += System.Text.Encoding.UTF8.GetByteCount(text.Substring(0, end + 1));
        PilotEvent last = null;
        foreach (var line in text.Substring(0, end).Split('\n'))
        {
            if (line.Trim().Length == 0) continue;
            try { last = JsonUtility.FromJson<PilotEvent>(line); Events.Add(last); }
            catch (Exception) { }
        }
        if (last == null) return;
        if (notify && last.kind != "info")
        {
            var content = new GUIContent($"{Icon(last.kind)} {last.title}");
            foreach (var view in Resources.FindObjectsOfTypeAll<EditorWindow>()
                         .Where(window => window is SceneView || window.GetType().Name == "GameView"))
                view.ShowNotification(content, 4);
        }
        Changed?.Invoke();
        UnityEditorInternal.InternalEditorUtility.RepaintAllViews();
    }

    /// A line of plain text (the probe's `note`), as an event of its own.
    public static void Note(string text)
    {
        var kind = text.StartsWith("✓") ? "patch" : text.StartsWith("✗") ? "broken" : text.StartsWith("⟳") ? "reload" : "info";
        var entry = new PilotEvent { time = DateTime.Now.ToString("HH:mm:ss"), kind = kind, title = text.TrimStart('✓', '✗', '⟳', ' ') };
        Directory.CreateDirectory(System.IO.Path.GetDirectoryName(Path));
        File.AppendAllText(Path, JsonUtility.ToJson(entry) + "\n");
    }

    public static void Clear()
    {
        if (File.Exists(Path)) File.WriteAllText(Path, "");
        read = 0;
        Events.Clear();
        Changed?.Invoke();
    }

    public static string Icon(string kind) => kind switch
    {
        "patch" => "✓",
        "same" => "·",
        "broken" => "✗",
        "failed" => "✗",
        "reload" => "⟳",
        "deleted" => "⟳",
        _ => "•",
    };

    public static Color Tint(string kind) => kind switch
    {
        "patch" => new Color(0.24f, 0.74f, 0.45f),
        "same" => new Color(0.55f, 0.58f, 0.62f),
        "broken" => new Color(0.92f, 0.33f, 0.33f),
        "failed" => new Color(0.92f, 0.33f, 0.33f),
        "reload" => new Color(0.96f, 0.66f, 0.2f),
        "deleted" => new Color(0.96f, 0.66f, 0.2f),
        _ => new Color(0.38f, 0.6f, 0.95f),
    };
}

public class PilotHotReloadWindow : EditorWindow
{
    [MenuItem("Window/Pilot Hot Reload")]
    static void Open()
    {
        var window = GetWindow<PilotHotReloadWindow>();
        window.titleContent = new GUIContent("Pilot Hot Reload");
        window.minSize = new Vector2(360, 300);
    }

    // The event shown in the card: the newest, or the one picked in the list.
    PilotEvent picked;
    VisualElement card, diff, list, stats;
    Label cardIcon, cardTitle, cardMeta, cardDetail, liveLabel;

    static bool Dark => EditorGUIUtility.isProSkin;
    static Color Surface => Dark ? new Color(0.17f, 0.17f, 0.18f) : new Color(0.96f, 0.96f, 0.97f);
    static Color Raised => Dark ? new Color(0.22f, 0.22f, 0.24f) : Color.white;
    static Color Line => Dark ? new Color(1, 1, 1, 0.08f) : new Color(0, 0, 0, 0.08f);
    static Color Ink => Dark ? new Color(0.92f, 0.92f, 0.93f) : new Color(0.12f, 0.12f, 0.14f);
    static Color Muted => Dark ? new Color(0.62f, 0.63f, 0.66f) : new Color(0.42f, 0.43f, 0.47f);

    void OnEnable() => PilotHud.Changed += Refresh;
    void OnDisable() => PilotHud.Changed -= Refresh;

    void CreateGUI()
    {
        var root = rootVisualElement;
        root.style.backgroundColor = Surface;
        root.style.paddingLeft = root.style.paddingRight = 12;
        root.style.paddingTop = 10;
        root.style.paddingBottom = 10;

        // Header: the name, whether the watcher is on, and the totals.
        var header = Row();
        header.style.justifyContent = Justify.SpaceBetween;
        header.style.marginBottom = 10;
        var name = Text("Pilot Hot Reload", 15, Ink, bold: true);
        header.Add(name);
        var live = Row();
        live.style.alignItems = Align.Center;
        var dot = new VisualElement();
        dot.style.width = dot.style.height = 8;
        Round(dot, 4);
        dot.style.backgroundColor = PilotHud.Tint("patch");
        dot.style.marginRight = 6;
        live.Add(dot);
        liveLabel = Text("watching", 11, Muted);
        live.Add(liveLabel);
        var clear = new Button(PilotHud.Clear) { text = "Clear" };
        clear.style.marginLeft = 10;
        live.Add(clear);
        header.Add(live);
        root.Add(header);

        stats = Row();
        stats.style.marginBottom = 10;
        root.Add(stats);

        // The card: one change, large.
        card = new VisualElement();
        card.style.backgroundColor = Raised;
        Round(card, 8);
        Border(card, Line);
        card.style.paddingLeft = card.style.paddingRight = 14;
        card.style.paddingTop = card.style.paddingBottom = 12;
        card.style.marginBottom = 12;
        var top = Row();
        top.style.alignItems = Align.Center;
        cardIcon = Text("", 18, Color.white, bold: true);
        cardIcon.style.width = cardIcon.style.height = 34;
        Round(cardIcon, 17);
        cardIcon.style.unityTextAlign = TextAnchor.MiddleCenter;
        cardIcon.style.marginRight = 12;
        cardIcon.style.flexShrink = 0;
        top.Add(cardIcon);
        var titles = new VisualElement();
        titles.style.flexGrow = 1;
        titles.style.flexShrink = 1;
        cardTitle = Text("", 16, Ink, bold: true);
        cardTitle.style.whiteSpace = WhiteSpace.Normal;
        cardMeta = Text("", 11, Muted);
        cardMeta.style.marginTop = 2;
        titles.Add(cardTitle);
        titles.Add(cardMeta);
        top.Add(titles);
        card.Add(top);
        cardDetail = Text("", 12, Muted);
        cardDetail.style.whiteSpace = WhiteSpace.Normal;
        cardDetail.style.marginTop = 8;
        card.Add(cardDetail);
        diff = new VisualElement();
        diff.style.marginTop = 10;
        Round(diff, 6);
        diff.style.overflow = Overflow.Hidden;
        diff.style.backgroundColor = Dark ? new Color(0.13f, 0.13f, 0.14f) : new Color(0.97f, 0.97f, 0.98f);
        Border(diff, Line);
        card.Add(diff);
        root.Add(card);

        root.Add(Text("HISTORY", 10, Muted, bold: true));
        var scroll = new ScrollView();
        scroll.style.flexGrow = 1;
        scroll.style.marginTop = 6;
        list = scroll.contentContainer;
        root.Add(scroll);

        Refresh();
    }

    void Refresh()
    {
        if (card == null) return;
        var events = PilotHud.Events.Where(entry => entry.kind != "info").ToList();
        var shown = picked != null && events.Contains(picked) ? picked : events.LastOrDefault();

        // Totals.
        stats.Clear();
        var patches = events.Where(entry => entry.kind == "patch").ToList();
        stats.Add(Stat(patches.Count.ToString(), "patched", PilotHud.Tint("patch")));
        stats.Add(Stat(patches.Count > 0 ? $"{patches.Average(entry => entry.seconds):0.0} s" : "—", "average", PilotHud.Tint("info")));
        stats.Add(Stat(events.Count(entry => entry.kind == "reload").ToString(), "reloads", PilotHud.Tint("reload")));
        stats.Add(Stat(events.Count(entry => entry.kind == "broken").ToString(), "not compiled", PilotHud.Tint("broken")));
        var info = PilotHud.Events.LastOrDefault(entry => entry.kind == "info");
        liveLabel.text = info?.title ?? "watching";

        // The card.
        if (shown == null)
        {
            cardIcon.text = "•";
            cardIcon.style.backgroundColor = PilotHud.Tint("info");
            cardTitle.text = "Save a file in Pilot";
            cardMeta.text = "what it changes shows here, without a reload";
            cardDetail.text = "";
            diff.Clear();
            diff.style.display = DisplayStyle.None;
        }
        else
        {
            cardIcon.text = PilotHud.Icon(shown.kind);
            cardIcon.style.backgroundColor = PilotHud.Tint(shown.kind);
            cardTitle.text = shown.title;
            var seconds = shown.seconds > 0 ? $"  ·  {shown.seconds:0.0} s" : "";
            cardMeta.text = $"{shown.file}{seconds}  ·  {shown.time}";
            cardDetail.text = shown.detail ?? "";
            cardDetail.style.display = string.IsNullOrEmpty(shown.detail) ? DisplayStyle.None : DisplayStyle.Flex;
            diff.Clear();
            var lines = shown.diff ?? Array.Empty<string>();
            diff.style.display = lines.Length > 0 ? DisplayStyle.Flex : DisplayStyle.None;
            foreach (var text in lines) diff.Add(DiffLine(text));
        }

        // The history, newest first.
        list.Clear();
        foreach (var entry in Enumerable.Reverse(events))
            list.Add(HistoryRow(entry, entry == shown));
    }

    VisualElement HistoryRow(PilotEvent entry, bool selected)
    {
        var row = Row();
        row.style.alignItems = Align.Center;
        row.style.paddingLeft = row.style.paddingRight = 8;
        row.style.paddingTop = row.style.paddingBottom = 6;
        row.style.marginBottom = 2;
        Round(row, 6);
        row.style.backgroundColor = selected ? Raised : Color.clear;
        var dot = new VisualElement();
        dot.style.width = dot.style.height = 8;
        Round(dot, 4);
        dot.style.backgroundColor = PilotHud.Tint(entry.kind);
        dot.style.marginRight = 8;
        dot.style.flexShrink = 0;
        row.Add(dot);
        var time = Text(entry.time, 11, Muted);
        time.style.width = 58;
        time.style.flexShrink = 0;
        row.Add(time);
        var title = Text(entry.title, 12, Ink);
        title.style.flexGrow = 1;
        title.style.flexShrink = 1;
        title.style.overflow = Overflow.Hidden;
        title.style.textOverflow = TextOverflow.Ellipsis;
        row.Add(title);
        var seconds = Text(entry.seconds > 0 ? $"{entry.seconds:0.0} s" : "", 11, Muted);
        seconds.style.marginLeft = 8;
        seconds.style.flexShrink = 0;
        row.Add(seconds);
        row.RegisterCallback<MouseEnterEvent>(_ => { if (!selected) row.style.backgroundColor = Line; });
        row.RegisterCallback<MouseLeaveEvent>(_ => { if (!selected) row.style.backgroundColor = Color.clear; });
        row.RegisterCallback<ClickEvent>(_ => { picked = entry; Refresh(); });
        return row;
    }

    static Font mono;
    static bool monoLooked;

    // The editor's own monospaced font, where this version has it.
    static Font Mono
    {
        get
        {
            if (!monoLooked)
            {
                monoLooked = true;
                mono = EditorGUIUtility.Load("Fonts/RobotoMono/RobotoMono-Regular.ttf") as Font;
            }
            return mono;
        }
    }

    static VisualElement DiffLine(string text)
    {
        var added = text.StartsWith("+");
        var removed = text.StartsWith("-");
        var label = new Label(text.Length > 0 ? text : " ");
        if (Mono != null) label.style.unityFontDefinition = FontDefinition.FromFont(Mono);
        label.style.fontSize = 11;
        label.style.paddingLeft = 8;
        label.style.paddingTop = label.style.paddingBottom = 1;
        label.style.whiteSpace = WhiteSpace.NoWrap;
        label.style.color = added ? new Color(0.35f, 0.82f, 0.5f) : removed ? new Color(0.95f, 0.45f, 0.45f) : Muted;
        if (added) label.style.backgroundColor = new Color(0.24f, 0.74f, 0.45f, 0.12f);
        if (removed) label.style.backgroundColor = new Color(0.92f, 0.33f, 0.33f, 0.12f);
        return label;
    }

    static VisualElement Stat(string value, string caption, Color tint)
    {
        var box = new VisualElement();
        box.style.flexGrow = 1;
        box.style.backgroundColor = Raised;
        Round(box, 6);
        Border(box, Line);
        box.style.paddingLeft = 10;
        box.style.paddingTop = box.style.paddingBottom = 6;
        box.style.marginRight = 6;
        var number = Text(value, 16, tint, bold: true);
        box.Add(number);
        box.Add(Text(caption, 10, Muted));
        return box;
    }

    static VisualElement Row()
    {
        var row = new VisualElement();
        row.style.flexDirection = FlexDirection.Row;
        return row;
    }

    static Label Text(string text, int size, Color color, bool bold = false)
    {
        var label = new Label(text);
        label.style.fontSize = size;
        label.style.color = color;
        if (bold) label.style.unityFontStyleAndWeight = FontStyle.Bold;
        return label;
    }

    static void Round(VisualElement element, float radius)
    {
        element.style.borderTopLeftRadius = element.style.borderTopRightRadius =
            element.style.borderBottomLeftRadius = element.style.borderBottomRightRadius = radius;
    }

    static void Border(VisualElement element, Color color)
    {
        element.style.borderTopWidth = element.style.borderBottomWidth =
            element.style.borderLeftWidth = element.style.borderRightWidth = 1;
        element.style.borderTopColor = element.style.borderBottomColor =
            element.style.borderLeftColor = element.style.borderRightColor = color;
    }
}
