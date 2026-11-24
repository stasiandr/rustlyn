// Checking that `include/rustlyn.h` describes the library it claims to.
//
// The header is written by hand, so nothing but a compiler makes the two
// agree. This includes the header, links the real static library, and asks
// the questions a wrong header would answer wrongly: are the structs laid out
// the same, do the enums still line up, and does a call through them actually
// work end to end.
//
// Run it with `crates/rustlyn-ffi/tests/run.sh`, which the workspace's CI
// does. It is C rather than Rust on purpose: a Rust test would be checking
// the library against itself.

#include "rustlyn.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int failures = 0;

#define CHECK(condition, ...)                                                  \
    do {                                                                       \
        if (!(condition)) {                                                    \
            printf("  FAIL %s:%d: ", __FILE__, __LINE__);                      \
            printf(__VA_ARGS__);                                               \
            printf("\n");                                                      \
            failures += 1;                                                     \
        }                                                                      \
    } while (0)

/// The bytes an RlnText names, copied into a NUL-terminated buffer.
static void read_text(const uint8_t *strings, RlnText slice, char *out, size_t capacity) {
    size_t length = slice.length < capacity - 1 ? slice.length : capacity - 1;
    memcpy(out, strings + slice.offset, length);
    out[length] = '\0';
}

static void write_file(const char *path, const char *text) {
    FILE *file = fopen(path, "w");
    assert(file != NULL);
    fputs(text, file);
    fclose(file);
}

// MARK: - the layout this header promises

static void check_layout(void) {
    printf("layout\n");

    // Sizes a mismatched header would get wrong. These are not arbitrary: a
    // field added on one side and not the other changes exactly this.
    CHECK(sizeof(RlnText) == 8, "RlnText is %zu bytes", sizeof(RlnText));
    CHECK(sizeof(RlnRun) == 12, "RlnRun is %zu bytes", sizeof(RlnRun));
    CHECK(sizeof(RlnDeclaration) == 92, "RlnDeclaration is %zu bytes",
          sizeof(RlnDeclaration));
    CHECK(sizeof(RlnLocation) == 32, "RlnLocation is %zu bytes", sizeof(RlnLocation));
    CHECK(sizeof(RlnCompletion) == 20, "RlnCompletion is %zu bytes", sizeof(RlnCompletion));
    CHECK(offsetof(RlnCompletions, start) == 4 * sizeof(size_t), "start moved");
    CHECK(offsetof(RlnCompiled, kind) == 3 * sizeof(size_t) + 8, "kind moved");
    CHECK(offsetof(RlnCompiled, unchanged) == 3 * sizeof(size_t) + 9, "unchanged moved");
    CHECK(sizeof(RlnRange) == 8, "RlnRange is %zu bytes", sizeof(RlnRange));
    CHECK(sizeof(RlnDiagnostic) == 28, "RlnDiagnostic is %zu bytes", sizeof(RlnDiagnostic));
    CHECK(sizeof(RlnSignature) == 16, "RlnSignature is %zu bytes", sizeof(RlnSignature));
    CHECK(sizeof(RlnDocParameter) == 16, "RlnDocParameter is %zu bytes", sizeof(RlnDocParameter));
    CHECK(sizeof(RlnEdit) == 24, "RlnEdit is %zu bytes", sizeof(RlnEdit));
    CHECK(sizeof(RlnRename) == 16, "RlnRename is %zu bytes", sizeof(RlnRename));
    CHECK(sizeof(RlnCodeAction) == 36, "RlnCodeAction is %zu bytes", sizeof(RlnCodeAction));
    CHECK(rln_action_kind_count() == RLN_ACTION_GENERATE + 1, "action kinds drifted");
    CHECK(offsetof(RlnDiagnostics, semantic) == 4 * sizeof(size_t), "semantic moved");
    CHECK(offsetof(RlnSignatures, active) == 6 * sizeof(size_t), "active moved");

    // Semantic colouring, highlights, detailed references, code lens.
    CHECK(sizeof(RlnSemanticRun) == 16, "RlnSemanticRun is %zu bytes", sizeof(RlnSemanticRun));
    CHECK(offsetof(RlnSemanticRun, class_) == 12, "class_ moved");
    CHECK(sizeof(RlnHighlight) == 12, "RlnHighlight is %zu bytes", sizeof(RlnHighlight));
    CHECK(sizeof(RlnReference) == 40, "RlnReference is %zu bytes", sizeof(RlnReference));
    CHECK(offsetof(RlnReference, line) == 24, "line moved");
    CHECK(sizeof(RlnLens) == 12, "RlnLens is %zu bytes", sizeof(RlnLens));
    CHECK(offsetof(RlnReferences, word) == 4 * sizeof(size_t), "word moved");
    CHECK(rln_semantic_class_count() == RLN_SEMANTIC_KEYWORD + 1,
          "the library knows %u semantic classes, this header %u",
          rln_semantic_class_count(), RLN_SEMANTIC_KEYWORD + 1);

    // Navigation.
    CHECK(sizeof(RlnHierarchyItem) == 72, "RlnHierarchyItem is %zu bytes", sizeof(RlnHierarchyItem));
    CHECK(sizeof(RlnLineRange) == 16, "RlnLineRange is %zu bytes", sizeof(RlnLineRange));
    CHECK(sizeof(RlnCall) == 92, "RlnCall is %zu bytes", sizeof(RlnCall));
    CHECK(sizeof(RlnSearchResult) == 60, "RlnSearchResult is %zu bytes", sizeof(RlnSearchResult));
    CHECK(offsetof(RlnHierarchyItem, kind) == 68, "kind moved");
    CHECK(offsetof(RlnCall, through_base) == 88, "through_base moved");
    CHECK(offsetof(RlnSearchResult, match_kind) == 56, "match_kind moved");

    // Inlay hints, analyzer tags, quick info.
    CHECK(offsetof(RlnDiagnostic, tags) == 9, "tags moved");
    CHECK(sizeof(RlnInlayHint) == 48, "RlnInlayHint is %zu bytes", sizeof(RlnInlayHint));
    CHECK(offsetof(RlnInlayHint, kind) == 44, "kind moved");
    CHECK(offsetof(RlnInlayHints, strings) == 2 * sizeof(size_t), "strings moved");
    CHECK(offsetof(RlnQuickInfo, parameters) == 80, "parameters moved");

    // Offsets: the fields the caller reads most, at the places it reads them.
    CHECK(offsetof(RlnDeclaration, name) == 0, "name moved");
    CHECK(offsetof(RlnRun, start) == 0, "start moved");
    CHECK(offsetof(RlnOutline, declarations) == 0, "declarations moved");
    CHECK(offsetof(RlnLocations, items) == 0, "items moved");

    // And the enums this header mirrors by hand.
    CHECK(rln_declaration_kind_count() == RLN_EXTENSION + 1,
          "the library knows %u declaration kinds, this header %u",
          rln_declaration_kind_count(), RLN_EXTENSION + 1);
    CHECK(rln_class_count() == RLN_DISABLED + 1,
          "the library knows %u classes, this header %u", rln_class_count(),
          RLN_DISABLED + 1);
    CHECK(rln_completion_kind_count() == RLN_COMPLETION_SNIPPET + 1,
          "the library knows %u completion kinds, this header %u",
          rln_completion_kind_count(), RLN_COMPLETION_SNIPPET + 1);
}

// MARK: - rename

/// Rename across the two files of the test project: `Health`, used in
/// Use.cs at `offset` and declared in Pawn.cs; and the class, with its file.
static void check_rename(RlnSession *session, const char *use_path, const char *use_text,
                         uint32_t offset) {
    CHECK(sizeof(RlnConflict) == 28, "RlnConflict is %zu bytes", sizeof(RlnConflict));
    CHECK(offsetof(RlnRenameInfo, strings) == 40, "strings moved");
    CHECK(offsetof(RlnRenameResult, conflicts) == 6 * sizeof(size_t), "conflicts moved");

    char name[256];
    RlnRenameInfo info = {0};
    RlnStatus status = rln_prepare_rename(session, use_path, NULL, offset, &info);
    CHECK(status == RLN_OK, "prepare_rename should answer, got %d", status);
    if (status == RLN_OK) {
        CHECK(info.can_rename, "Health can be renamed");
        CHECK(info.start == offset && info.length == 6, "the box goes on the name");
        read_text(info.strings, info.text, name, sizeof name);
        CHECK(strcmp(name, "Health") == 0, "the placeholder was %s", name);
        rln_rename_info_free(info);
    }
    status = rln_prepare_rename(session, use_path, NULL, 0, &info);
    CHECK(status == RLN_OK && !info.can_rename && info.refused.length > 0,
          "the `namespace` keyword cannot be renamed, and says why");
    if (status == RLN_OK) {
        rln_rename_info_free(info);
    }

    RlnRenameResult result = {0};
    status = rln_rename(session, use_path, NULL, offset, "Life", RLN_RENAME_FILE, &result);
    CHECK(status == RLN_OK, "rename should answer, got %d", status);
    if (status == RLN_OK) {
        CHECK(result.refused.length == 0, "the rename is done");
        CHECK(result.edits.count == 2, "the declaration and the use, got %zu", result.edits.count);
        CHECK(result.conflict_count == 0, "no conflicts, got %zu", result.conflict_count);
        int files = 0;
        for (size_t index = 0; index < result.edits.count; index += 1) {
            RlnEdit edit = result.edits.items[index];
            read_text(result.edits.strings, edit.text, name, sizeof name);
            CHECK(strcmp(name, "Life") == 0 && edit.length == 6, "each edit writes the new name");
            read_text(result.edits.strings, edit.path, name, sizeof name);
            if (strstr(name, "Pawn.cs") != NULL || strstr(name, "Use.cs") != NULL) {
                files += 1;
            }
        }
        CHECK(files == 2, "one edit in each file");
        CHECK(result.edits.rename_count == 0, "a field has no file");
        rln_rename_result_free(result);
    }

    // The class, from its use in the other file: its file follows it.
    uint32_t pawn = (uint32_t)(strstr(use_text, "Pawn p") - use_text);
    status = rln_rename(session, use_path, NULL, pawn, "Piece", RLN_RENAME_FILE, &result);
    CHECK(status == RLN_OK && result.edits.rename_count == 1, "Pawn.cs becomes Piece.cs");
    if (status == RLN_OK) {
        if (result.edits.rename_count == 1) {
            read_text(result.edits.strings, result.edits.renames[0].to, name, sizeof name);
            CHECK(strstr(name, "Piece.cs") != NULL, "renamed to %s", name);
        }
        rln_rename_result_free(result);
    }

    // Not an identifier: refused, with nothing to apply.
    status = rln_rename(session, use_path, NULL, offset, "1x", 0, &result);
    CHECK(status == RLN_OK && result.refused.length > 0 && result.edits.count == 0,
          "`1x` is not a name");
    if (status == RLN_OK) {
        rln_rename_result_free(result);
    }
}

// MARK: - navigation

/// Type definition, bases, implementations, the hierarchies and Navigate To,
/// on the compiled two-file project `check_calls` builds.
static void check_navigation(RlnSession *session, const char *pawn_path, const char *use_path,
                             const char *use_text) {
    printf("navigation\n");
    char name[256];

    // `p` is a Pawn: its type is declared in Pawn.cs.
    uint32_t p = (uint32_t)(strstr(use_text, "p.Health") - use_text);
    RlnLocations types = {0};
    RlnStatus status = rln_type_definition(session, use_path, NULL, p, &types);
    CHECK(status == RLN_OK, "the type of p should be found, got %d", status);
    if (status == RLN_OK) {
        CHECK(types.count == 1, "one type, got %zu", types.count);
        if (types.count == 1) {
            read_text(types.strings, types.items[0].name, name, sizeof name);
            CHECK(strcmp(name, "Game.Pawn") == 0, "the type was %s", name);
        }
        rln_locations_free(types);
    }

    // Pawn derives from nothing the project declares; its bases are in the
    // core library, which has no file here.
    RlnLocations bases = {0};
    status = rln_bases(session, use_path, NULL, p, &bases);
    CHECK(status == RLN_OK, "bases should come back, got %d", status);
    if (status == RLN_OK) {
        rln_locations_free(bases);
    }
    RlnLocations implementations = {0};
    status = rln_implementations_in(session, pawn_path, NULL, 30, &implementations);
    CHECK(status == RLN_OK, "implementations should come back, got %d", status);
    if (status == RLN_OK) {
        CHECK(implementations.count == 1, "Pawn is its own, got %zu", implementations.count);
        rln_locations_free(implementations);
    }
    RlnLocations derived = {0};
    status = rln_derived_types(session, pawn_path, NULL, 30, false, &derived);
    CHECK(status == RLN_OK && derived.count == 0, "nothing derives from Pawn");
    if (status == RLN_OK) {
        rln_locations_free(derived);
    }

    // The call hierarchy of M: nobody calls it, and it calls nothing but
    // reads a field, which is not a call.
    uint32_t m = (uint32_t)(strstr(use_text, "M(Pawn") - use_text);
    RlnHierarchyItems root = {0};
    status = rln_call_hierarchy(session, use_path, NULL, m, &root);
    CHECK(status == RLN_OK, "M should be an item, got %d", status);
    if (status == RLN_OK) {
        CHECK(root.count == 1, "one root, got %zu", root.count);
        if (root.count == 1) {
            const RlnHierarchyItem *item = &root.items[0];
            read_text(root.strings, item->name, name, sizeof name);
            CHECK(strcmp(name, "M") == 0, "the item was %s", name);
            CHECK(item->kind == RLN_METHOD, "M is a method");
            CHECK(item->has_location && item->line == 1, "M is on line 1");
            char key[256];
            read_text(root.strings, item->key, key, sizeof key);
            RlnCalls calls = {0};
            CHECK(rln_incoming_calls(session, key, &calls) == RLN_OK, "incoming calls");
            CHECK(calls.count == 0, "nobody calls M, got %zu", calls.count);
            rln_calls_free(calls);
            CHECK(rln_outgoing_calls(session, key, &calls) == RLN_OK, "outgoing calls");
            CHECK(calls.count == 0, "M calls nothing, got %zu", calls.count);
            rln_calls_free(calls);
        }
        rln_hierarchy_items_free(root);
    }
    RlnCalls none = {0};
    CHECK(rln_incoming_calls(session, "M:Nowhere|Gone`0()", &none) == RLN_NOT_IN_PROJECT,
          "a key that names nothing is refused");

    // The type hierarchy of Pawn, one level each way.
    RlnHierarchyItems pawn = {0};
    status = rln_type_hierarchy(session, use_path, NULL, p, &pawn);
    CHECK(status == RLN_OK && pawn.count == 1, "Pawn should be an item, got %d", status);
    if (status == RLN_OK) {
        char key[256];
        read_text(pawn.strings, pawn.items[0].key, key, sizeof key);
        CHECK(strcmp(key, "T:Game.Pawn") == 0, "the key was %s", key);
        RlnHierarchyItems up = {0};
        CHECK(rln_supertypes(session, key, &up) == RLN_OK, "supertypes");
        CHECK(up.count == 1, "object above Pawn, got %zu", up.count);
        rln_hierarchy_items_free(up);
        RlnHierarchyItems down = {0};
        CHECK(rln_subtypes(session, key, &down) == RLN_OK, "subtypes");
        CHECK(down.count == 0, "nothing below Pawn, got %zu", down.count);
        rln_hierarchy_items_free(down);
        rln_hierarchy_items_free(pawn);
    }

    // Navigate To, by capitals.
    RlnSearchResults results = {0};
    status = rln_search(session, "pa", RLN_SEARCH_ALL, 10, &results);
    CHECK(status == RLN_OK, "search should answer, got %d", status);
    if (status == RLN_OK) {
        CHECK(results.count == 2, "Pawn and Pawn.cs, got %zu", results.count);
        if (results.count > 0) {
            const RlnSearchResult *first = &results.items[0];
            read_text(results.strings, first->name, name, sizeof name);
            CHECK(strcmp(name, "Pawn") == 0, "the first was %s", name);
            CHECK(first->match_kind == RLN_MATCH_PREFIX, "a prefix, got %u", first->match_kind);
            CHECK(!first->is_file, "a type first");
            CHECK(first->range_count == 1, "one range");
            RlnRange range = results.ranges[first->first_range];
            CHECK(range.start == 0 && range.end == 2, "the first two letters");
            CHECK(first->location.line == 1, "on line 1");
        }
        rln_search_results_free(results);
    }
    CHECK(rln_search(session, "pa", 9, 10, &results) == RLN_BAD_ARGUMENT,
          "an unknown kind is refused");
}

// MARK: - completion parity

/// Completion items with their insert texts and edits, descriptions and the
/// trigger, on the test project's Use.cs as if typed.
static void check_completion_items(RlnSession *session, const char *use_path) {
    CHECK(sizeof(RlnCompletionItem) == 56, "RlnCompletionItem is %zu bytes",
          sizeof(RlnCompletionItem));
    CHECK(offsetof(RlnCompletionItem, kind) == 52, "kind moved");
    CHECK(sizeof(RlnTextEdit) == 16, "RlnTextEdit is %zu bytes", sizeof(RlnTextEdit));
    CHECK(offsetof(RlnCompletionItems, start) == 6 * sizeof(size_t), "start moved");

    char name[512];
    const char *typed =
        "namespace Game;\npublic class Use { void M(Pawn p) { Pawn q = new  } }\n";
    uint32_t after_new = (uint32_t)(strstr(typed, "new  }") - typed) + 4;
    RlnCompletionItems list = {0};
    RlnStatus status = rln_completions_ex(session, use_path, typed, after_new, &list);
    CHECK(status == RLN_OK, "it should complete, got %d", status);
    if (status == RLN_OK) {
        int preselected = 0;
        for (size_t index = 0; index < list.count; index += 1) {
            RlnCompletionItem item = list.items[index];
            read_text(list.strings, item.label, name, sizeof name);
            if (item.preselect) {
                preselected = strcmp(name, "Pawn") == 0;
            }
            CHECK(item.kind != RLN_COMPLETION_KEYWORD || strcmp(name, "if") != 0,
                  "no statements after `new`");
            CHECK(item.edits_start + item.edits_count <= list.edit_count, "edits in range");
        }
        CHECK(preselected, "Pawn is preselected after `new`");
        CHECK(!list.suggestion_mode, "a type is not a new name");
        rln_completion_items_free(list);
    }

    // A snippet in a statement, with its caret.
    const char *statement = "namespace Game;\npublic class Use { void M(Pawn p) {  } }\n";
    uint32_t inside = (uint32_t)(strstr(statement, "{  }") - statement) + 2;
    status = rln_completions_ex(session, use_path, statement, inside, &list);
    CHECK(status == RLN_OK, "it should complete, got %d", status);
    if (status == RLN_OK) {
        int saw_cw = 0;
        for (size_t index = 0; index < list.count; index += 1) {
            RlnCompletionItem item = list.items[index];
            read_text(list.strings, item.label, name, sizeof name);
            if (strcmp(name, "cw") == 0 && item.kind == RLN_COMPLETION_SNIPPET) {
                saw_cw = item.is_snippet && item.caret == strlen("Console.WriteLine(");
            }
        }
        CHECK(saw_cw, "cw is a snippet with its caret in the parentheses");
        rln_completion_items_free(list);
    }

    // The description of `Health` after `p.`.
    const char *dotted =
        "namespace Game;\npublic class Use { void M(Pawn p) { p. } }\n";
    uint32_t dot = (uint32_t)(strstr(dotted, "p. }") - dotted) + 2;
    RlnDocumentation documentation = {0};
    status = rln_completion_description(session, use_path, dotted, dot, "Health", &documentation);
    CHECK(status == RLN_OK, "Health should be described, got %d", status);
    if (status == RLN_OK) {
        read_text(documentation.strings, documentation.signature, name, sizeof name);
        CHECK(strcmp(name, "int Health") == 0, "the signature was %s", name);
        rln_documentation_free(documentation);
    }

    bool opens = false;
    CHECK(rln_completion_trigger(session, dotted, dot, '.', &opens) == RLN_OK && opens,
          "a dot opens the list");
    CHECK(rln_completion_trigger(session, dotted, dot, 0xD800, &opens) == RLN_BAD_ARGUMENT,
          "a surrogate is not a character");
}

// MARK: - inlay hints, quick info

/// `Use.cs` is `... void M(Pawn p) { var n = p.Health; } ...`.
static void check_insight(RlnSession *session, const char *use_path, const char *use_text) {
    char name[256];

    // `var n` gets its type, in front of `n`, with a space after it.
    RlnInlayHints hints = {0};
    RlnStatus status = rln_inlay_hints(session, use_path, NULL, 0, (uint32_t)strlen(use_text),
                                       rln_inlay_default_options(), &hints);
    CHECK(status == RLN_OK, "inlay hints should come back, got %d", status);
    if (status == RLN_OK) {
        CHECK(hints.count == 1, "one hint, got %zu", hints.count);
        if (hints.count > 0) {
            RlnInlayHint hint = hints.items[0];
            read_text(hints.strings, hint.label, name, sizeof name);
            CHECK(strcmp(name, "int") == 0, "the hint was %s", name);
            CHECK(hint.kind == 0, "a type hint");
            CHECK(hint.position == (uint32_t)(strstr(use_text, "n =") - use_text), "before n");
            CHECK(hint.flags & RLN_INLAY_PADDING_RIGHT, "a space after it");
            CHECK(hint.flags & RLN_INLAY_HAS_REPLACEMENT, "double-clicking writes the type");
            read_text(hints.strings, hint.replace_text, name, sizeof name);
            CHECK(strcmp(name, "int") == 0 && hint.replace_length == 3, "`var` becomes `int`");
        }
        rln_inlay_hints_free(hints);
    }
    CHECK(rln_inlay_hints(session, use_path, NULL, 0, (uint32_t)strlen(use_text),
                          RLN_INLAY_PARAMETERS, &hints) == RLN_OK,
          "parameter hints only");
    CHECK(hints.count == 0, "no call here has a literal argument");
    rln_inlay_hints_free(hints);

    // Quick info on `Health`, and on `var`.
    RlnQuickInfo info = {0};
    uint32_t health = (uint32_t)(strstr(use_text, "Health") - use_text);
    status = rln_quick_info(session, use_path, NULL, health, &info);
    CHECK(status == RLN_OK, "quick info should come back, got %d", status);
    if (status == RLN_OK) {
        read_text(info.strings, info.description, name, sizeof name);
        CHECK(strcmp(name, "(field) int Pawn.Health") == 0, "the description was %s", name);
        CHECK(info.start == health && info.length == 6, "about the name");
        CHECK(info.summary.length == 0 && info.parameter_count == 0, "nothing documented");
        rln_quick_info_free(info);
    }
    status = rln_quick_info(session, use_path, NULL,
                            (uint32_t)(strstr(use_text, "var") - use_text), &info);
    CHECK(status == RLN_OK, "quick info on var, got %d", status);
    if (status == RLN_OK) {
        read_text(info.strings, info.description, name, sizeof name);
        CHECK(strcmp(name, "struct System.Int32") == 0, "var is %s", name);
        rln_quick_info_free(info);
    }
    CHECK(rln_quick_info(session, use_path, NULL, (uint32_t)(strstr(use_text, "{") - use_text),
                         &info) == RLN_NOT_A_NAME,
          "a brace has no quick info");
}

// MARK: - .editorconfig, fix all, completion filtering

static void check_configured(RlnSession *session, const char *directory, const char *use_path) {
    CHECK(sizeof(RlnSetting) == 16, "RlnSetting is %zu bytes", sizeof(RlnSetting));
    CHECK(sizeof(RlnFilteredItem) == 8, "RlnFilteredItem is %zu bytes", sizeof(RlnFilteredItem));
    char name[256];

    // Settings from an .editorconfig whose sections only reach a folder of
    // their own, so the other checks format as they always did.
    char config[1024], file[1024];
    snprintf(config, sizeof config, "%s/.editorconfig", directory);
    snprintf(file, sizeof file, "%s/configured/Any.cs", directory);
    write_file(config, "root = true\n[configured/*.cs]\nindent_size = 2\nIndent_Style = space\n"
                       "[configured/*.txt]\nindent_size = 8\n");
    RlnSettings settings = {0};
    RlnStatus status = rln_editorconfig(session, file, &settings);
    CHECK(status == RLN_OK, "settings should come back, got %d", status);
    if (status == RLN_OK) {
        CHECK(settings.count == 2, "two settings for a .cs file, got %zu", settings.count);
        if (settings.count == 2) {
            read_text(settings.strings, settings.items[0].key, name, sizeof name);
            CHECK(strcmp(name, "indent_size") == 0, "the first key was %s", name);
            read_text(settings.strings, settings.items[0].value, name, sizeof name);
            CHECK(strcmp(name, "2") == 0, "indent_size was %s", name);
        }
        rln_settings_free(settings);
    }
    CHECK(rln_editorconfig(session, NULL, &settings) == RLN_BAD_ARGUMENT, "a null path is refused");

    // Fix all: `n` is assigned and never read.
    RlnEdits edits = {0};
    status = rln_fix_all(session, use_path, NULL, "IDE0059", RLN_FIX_ALL_DOCUMENT, &edits);
    CHECK(status == RLN_OK, "fix all should come back, got %d", status);
    if (status == RLN_OK) {
        rln_edits_free(edits);
    }
    status = rln_fix_all(session, use_path, NULL, "CS0000", RLN_FIX_ALL_PROJECT, &edits);
    CHECK(status == RLN_OK && edits.count == 0, "nothing to fix is no edits, got %d", status);
    if (status == RLN_OK) {
        rln_edits_free(edits);
    }
    CHECK(rln_fix_all(session, use_path, NULL, "IDE0059", 7, &edits) == RLN_BAD_ARGUMENT,
          "an unknown scope is refused");

    // Completion filtering, Roslyn's order.
    const char *names[4] = {"GetHashCode", "GoToDefinition", "gtd", "Other"};
    RlnFilteredItems filtered = {0};
    status = rln_completion_filter(names, 4, "GTD", &filtered);
    CHECK(status == RLN_OK, "filtering should come back, got %d", status);
    if (status == RLN_OK) {
        CHECK(filtered.count == 2, "two names match GTD, got %zu", filtered.count);
        if (filtered.count == 2) {
            CHECK(filtered.items[0].index == 2 && filtered.items[0].kind == RLN_MATCH_EXACT,
                  "gtd first, as an exact match");
            CHECK(filtered.items[1].index == 1 &&
                      filtered.items[1].kind == RLN_MATCH_CAMEL_CASE_EXACT,
                  "then GoToDefinition by its humps");
        }
        rln_filtered_items_free(filtered);
    }
    CHECK(rln_completion_filter(NULL, 1, "a", &filtered) == RLN_BAD_ARGUMENT,
          "no names is refused");
}

// MARK: - the calls, end to end

static void check_calls(const char *directory) {
    printf("calls\n");

    char pawn_path[1024], use_path[1024];
    snprintf(pawn_path, sizeof pawn_path, "%s/Pawn.cs", directory);
    snprintf(use_path, sizeof use_path, "%s/Use.cs", directory);

    write_file(pawn_path,
               "namespace Game;\npublic class Pawn { public int Health; public void Hit(int a, int b) { } }\n");
    const char *use_text =
        "namespace Game;\npublic class Use { void M(Pawn p) { var n = p.Health; } }\n";
    write_file(use_path, use_text);

    RlnSession *session = rln_session_new(directory, NULL, NULL, 0);
    CHECK(session != NULL, "the session should open");
    if (session == NULL) {
        return;
    }

    // Layer 1.
    CHECK(rln_open(session, use_path) == RLN_OK, "Use.cs should open");

    // Layer 2.
    RlnRuns runs = {NULL, 0};
    CHECK(rln_classify(session, use_path, 0, 1, &runs) == RLN_OK, "it should colour");
    int saw_keyword = 0;
    for (size_t index = 0; index < runs.count; index += 1) {
        if (runs.items[index].class_ == RLN_KEYWORD) {
            saw_keyword = 1;
        }
    }
    CHECK(saw_keyword, "there should be a keyword in `public class Use`");
    rln_runs_free(runs);

    // Layer 3.
    RlnOutline outline = {0};
    CHECK(rln_outline(session, use_path, &outline) == RLN_OK, "it should outline");
    int saw_method = 0;
    char name[256];
    for (size_t index = 0; index < outline.count; index += 1) {
        read_text(outline.strings, outline.declarations[index].name, name, sizeof name);
        if (strcmp(name, "M") == 0) {
            saw_method = 1;
            CHECK(outline.declarations[index].kind == RLN_METHOD, "M should be a method");
            CHECK(outline.declarations[index].parameter_count == 1, "M takes one parameter");
        }
    }
    CHECK(saw_method, "the outline should hold M");
    read_text(outline.strings, outline.namespaces, name, sizeof name);
    CHECK(strcmp(name, "Game") == 0, "the namespace should be Game, was %s", name);
    rln_outline_free(outline);

    // Layer 4.
    const char *paths[2] = {pawn_path, use_path};
    RlnReport report = {0};
    CHECK(rln_reindex(session, paths, 2, &report) == RLN_OK, "it should index");
    CHECK(report.files == 2, "two files, saw %zu", report.files);

    // `p.Health` — the offset of `Health` in the text above.
    const char *at = strstr(use_text, "Health");
    CHECK(at != NULL, "the test text should contain Health");
    uint32_t offset = (uint32_t)(at - use_text);

    RlnLocations locations = {0};
    RlnStatus status = rln_definition(session, use_path, offset, &locations);
    CHECK(status == RLN_OK, "it should resolve, got %d", status);
    if (status == RLN_OK) {
        CHECK(locations.certain, "the scope should settle it");
        CHECK(locations.count == 1, "one target, got %zu", locations.count);
        read_text(locations.strings, locations.word, name, sizeof name);
        CHECK(strcmp(name, "Health") == 0, "the word should be Health, was %s", name);
        if (locations.count > 0) {
            read_text(locations.strings, locations.items[0].path, name, sizeof name);
            CHECK(strcmp(name, "Pawn.cs") == 0, "it should lead to Pawn.cs, was %s", name);
            read_text(locations.strings, locations.items[0].name, name, sizeof name);
            CHECK(strcmp(name, "Game.Pawn.Health") == 0, "was %s", name);
        }
        rln_locations_free(locations);
    }

    // Layer 6: before compiling, the compiler has nothing to say.
    RlnLocations uses = {0};
    CHECK(rln_references(session, use_path, NULL, offset, &uses) == RLN_NOT_COMPILED,
          "references need a compilation");

    RlnCompiled compiled = {0};
    CHECK(rln_compile(session, paths, 2, &compiled) == RLN_OK, "it should compile");
    CHECK(compiled.files == 2, "two files compiled, saw %zu", compiled.files);
    CHECK(!compiled.unchanged, "the first compilation is new");
    CHECK(rln_save_compilation(session) == RLN_OK, "it should save");

    // A second session over the same cache reads the compilation back.
    char cache[1024];
    snprintf(cache, sizeof cache, "%s/cache", directory);
    RlnSession *cached = rln_session_new(directory, cache, NULL, 0);
    CHECK(rln_load_compilation(cached, NULL) == RLN_NOT_COMPILED, "nothing saved there yet");
    rln_compile(cached, paths, 2, NULL);
    CHECK(rln_save_compilation(cached) == RLN_OK, "saved to the cache");
    rln_session_free(cached);
    RlnSession *reopened = rln_session_new(directory, cache, NULL, 0);
    RlnCompiled loaded = {0};
    CHECK(rln_load_compilation(reopened, &loaded) == RLN_OK, "the saved compilation reads back");
    CHECK(loaded.files == 2, "with its two files, saw %zu", loaded.files);
    rln_compile(reopened, paths, 2, &loaded);
    CHECK(loaded.unchanged, "and compiling finds nothing changed");
    rln_session_free(reopened);

    status = rln_references(session, use_path, NULL, offset, &uses);
    CHECK(status == RLN_OK, "references should be found, got %d", status);
    if (status == RLN_OK) {
        // The declaration in Pawn.cs and the use in Use.cs.
        CHECK(uses.count == 2, "two uses, got %zu", uses.count);
        rln_locations_free(uses);
    }

    // Completion in text that was never saved: a dot after `p`.
    const char *typed =
        "namespace Game;\npublic class Use { void M(Pawn p) { var n = p.Health; p. } }\n";
    uint32_t dot = (uint32_t)(strstr(typed, "p. }") - typed) + 2;
    RlnCompletions completions = {0};
    status = rln_completions(session, use_path, typed, dot, &completions);
    CHECK(status == RLN_OK, "it should complete, got %d", status);
    if (status == RLN_OK) {
        int saw_health = 0;
        for (size_t index = 0; index < completions.count; index += 1) {
            read_text(completions.strings, completions.items[index].label, name, sizeof name);
            if (strcmp(name, "Health") == 0) {
                saw_health = 1;
                CHECK(completions.items[index].kind == RLN_COMPLETION_FIELD, "Health is a field");
                read_text(completions.strings, completions.items[index].detail, name, sizeof name);
                CHECK(strcmp(name, "int Health") == 0, "the detail was %s", name);
            }
        }
        CHECK(saw_health, "Health should be offered after `p.`");
        CHECK(completions.start == dot, "the word starts at the cursor");
        rln_completions_free(completions);
    }

    RlnString described = {0};
    CHECK(rln_describe(session, use_path, NULL, offset, &described) == RLN_OK, "it should describe");
    if (described.bytes != NULL) {
        CHECK(described.length == strlen("int Health")
                  && memcmp(described.bytes, "int Health", described.length) == 0,
              "Health should read as `int Health`");
        rln_text_free(described);
    }

    // What is wrong with a file, before saving: an unknown name.
    const char *broken =
        "namespace Game;\npublic class Use { void M(Pawn p) { var n = missing; } }\n";
    RlnDiagnostics diagnostics = {0};
    status = rln_diagnostics(session, use_path, broken, &diagnostics);
    CHECK(status == RLN_OK, "diagnostics should come back, got %d", status);
    if (status == RLN_OK) {
        CHECK(diagnostics.semantic, "the compiler looked");
        // The error, and the IDE analyzers' suggestion that the private `M`
        // nobody calls could go.
        CHECK(diagnostics.count == 2, "an error and a suggestion, got %zu", diagnostics.count);
        int saw_error = 0, saw_unused = 0;
        for (size_t index = 0; index < diagnostics.count; index += 1) {
            RlnDiagnostic item = diagnostics.items[index];
            read_text(diagnostics.strings, item.code, name, sizeof name);
            if (item.severity == 3) {
                saw_error = 1;
                CHECK(strcmp(name, "CS0103") == 0, "the code was %s", name);
                CHECK(item.start == (uint32_t)(strstr(broken, "missing") - broken), "at the name");
                CHECK(item.length == 7, "the name's length");
                CHECK(item.tags == 0, "an error is not faded");
            } else if (strcmp(name, "IDE0051") == 0) {
                saw_unused = 1;
                CHECK(item.severity == 1, "a suggestion");
                CHECK(item.tags & RLN_DIAGNOSTIC_UNNECESSARY, "drawn faded");
                CHECK(item.start == (uint32_t)(strstr(broken, "M(") - broken), "at M");
            }
        }
        CHECK(saw_error && saw_unused, "the error and IDE0051");
        rln_diagnostics_free(diagnostics);
    }

    // MARK: - code fixes
    // The light bulb on a type name spelled wrong in unsaved text (CS0246).
    const char *misspelled =
        "namespace Game;\npublic class Use { void M(Pawnn p) { var n = p.Health; } }\n";
    CHECK(!rln_is_generated(session, use_path), "a script is not generated code");
    CHECK(!rln_is_generated(NULL, use_path), "a null session is not an answer");

    RlnCodeActions fixes = {0};
    uint32_t on_type = (uint32_t)(strstr(misspelled, "Pawnn") - misspelled) + 1;
    status = rln_code_actions(session, use_path, misspelled, on_type, on_type, &fixes);
    CHECK(status == RLN_OK, "code actions should come back, got %d", status);
    if (status == RLN_OK) {
        int respell = -1;
        for (size_t i = 0; i < fixes.count; i++) {
            read_text(fixes.strings, fixes.items[i].title, name, sizeof name);
            if (strcmp(name, "Change 'Pawnn' to 'Pawn'.") == 0) {
                respell = (int)i;
            }
        }
        CHECK(respell >= 0, "the spelling fix should be offered");
        if (respell >= 0) {
            RlnCodeAction action = fixes.items[respell];
            read_text(fixes.strings, action.fixes, name, sizeof name);
            CHECK(strcmp(name, "CS0246") == 0, "it fixes CS0246, not %s", name);
            CHECK(action.kind == RLN_ACTION_QUICK_FIX, "a quick fix");
            CHECK(action.edit_count == 1, "one edit, got %u", action.edit_count);
            if (action.edit_count == 1) {
                RlnEdit edit = fixes.edits[action.first_edit];
                read_text(fixes.strings, edit.text, name, sizeof name);
                CHECK(strcmp(name, "Pawn") == 0, "the edit writes %s", name);
                CHECK(edit.start == on_type - 1 && edit.length == 5, "over the name");
            }
        }
        rln_code_actions_free(fixes);
    }

    // The signature of a call being typed.
    const char *calling =
        "namespace Game;\npublic class Use { void M(Pawn p) { var n = p.Health; p.Hit(1, ); } }\n";
    RlnSignatures signatures = {0};
    status = rln_signatures(session, use_path, calling,
                            (uint32_t)(strstr(calling, ", )") - calling) + 2, &signatures);
    CHECK(status == RLN_OK, "signatures should come back, got %d", status);
    if (status == RLN_OK) {
        CHECK(signatures.count == 1, "one overload, got %zu", signatures.count);
        CHECK(signatures.parameter == 1, "at the second parameter, got %u", signatures.parameter);
        if (signatures.count > 0) {
            read_text(signatures.strings, signatures.items[0].label, name, sizeof name);
            CHECK(strcmp(name, "void Hit(int a, int b)") == 0, "the label was %s", name);
            RlnRange second = signatures.parameters[signatures.items[0].first_parameter + 1];
            CHECK(second.end - second.start == strlen("int b"), "the second parameter's range");
        }
        rln_signatures_free(signatures);
    }

    // Documentation, and extend selection.
    RlnDocumentation documentation = {0};
    status = rln_documentation(session, use_path, NULL, offset, &documentation);
    CHECK(status == RLN_OK, "documentation should come back, got %d", status);
    if (status == RLN_OK) {
        read_text(documentation.strings, documentation.signature, name, sizeof name);
        CHECK(strcmp(name, "int Health") == 0, "the signature was %s", name);
        rln_documentation_free(documentation);
    }
    RlnRanges ranges = {0};
    status = rln_selection_ranges(session, use_path, NULL, offset, offset, &ranges);
    CHECK(status == RLN_OK && ranges.count > 2, "ranges around the name, got %zu", ranges.count);
    if (status == RLN_OK) {
        CHECK(ranges.items[0].end - ranges.items[0].start == strlen("Health"), "first the name");
        rln_ranges_free(ranges);
    }

    // Semantic colouring: `Health` in `p.Health` is a field, `var` a keyword.
    RlnSemanticRuns semantic_runs = {0};
    status = rln_semantic_tokens(session, use_path, NULL, 0, (uint32_t)strlen(use_text),
                                 &semantic_runs);
    CHECK(status == RLN_OK, "semantic tokens should come back, got %d", status);
    if (status == RLN_OK) {
        int saw_field = 0, saw_var = 0;
        uint32_t var_at = (uint32_t)(strstr(use_text, "var") - use_text);
        for (size_t index = 0; index < semantic_runs.count; index += 1) {
            RlnSemanticRun run = semantic_runs.items[index];
            if (run.start == offset && run.class_ == RLN_SEMANTIC_FIELD_NAME) {
                saw_field = 1;
            }
            if (run.start == var_at && run.class_ == RLN_SEMANTIC_KEYWORD) {
                saw_var = 1;
            }
        }
        CHECK(saw_field, "Health should be a field name");
        CHECK(saw_var, "var should be a keyword");
        rln_semantic_runs_free(semantic_runs);
    }

    // Highlights: `n` declared, nothing else in the file uses it.
    RlnHighlights highlights = {0};
    status = rln_highlights(session, use_path, NULL,
                            (uint32_t)(strstr(use_text, "n =") - use_text), &highlights);
    CHECK(status == RLN_OK, "highlights should come back, got %d", status);
    if (status == RLN_OK) {
        CHECK(highlights.count == 1, "one highlight, got %zu", highlights.count);
        if (highlights.count > 0) {
            CHECK(highlights.items[0].kind == RLN_HIGHLIGHT_DEFINITION, "the declaration");
        }
        rln_highlights_free(highlights);
    }

    // The references list, with where each one is and what it does.
    RlnReferences detailed = {0};
    status = rln_references_detailed(session, use_path, NULL, offset, &detailed);
    CHECK(status == RLN_OK, "detailed references should come back, got %d", status);
    if (status == RLN_OK) {
        CHECK(detailed.count == 2, "two references, got %zu", detailed.count);
        for (size_t index = 0; index < detailed.count; index += 1) {
            RlnReference reference = detailed.items[index];
            read_text(detailed.strings, reference.path, name, sizeof name);
            if (strcmp(name, "Use.cs") == 0) {
                CHECK(reference.kind == RLN_REFERENCE_READ, "a read");
                CHECK(reference.line == 1, "on the second line, got %u", reference.line);
                read_text(detailed.strings, reference.container, name, sizeof name);
                CHECK(strcmp(name, "Use.M") == 0, "in Use.M, was %s", name);
            } else {
                CHECK(reference.kind == RLN_REFERENCE_DEFINITION, "the declaration");
            }
        }
        rln_references_free(detailed);
    }

    // A cancel calls off counts already running, not the ones after it.
    rln_cancel_code_lens(session);
    CHECK(RLN_CANCELLED == 12, "the status of a count called off");

    // Where the lenses of Pawn.cs go, before anything is counted.
    RlnLenses places = {0};
    status = rln_code_lens_places(session, pawn_path, NULL, &places);
    CHECK(status == RLN_OK, "lens places should come back, got %d", status);
    if (status == RLN_OK) {
        CHECK(places.count == 3, "a type, a field and a method, got %zu", places.count);
        for (size_t i = 0; i < places.count; i++) {
            CHECK(places.items[i].count == UINT32_MAX, "not counted, got %u", places.items[i].count);
        }
        rln_lenses_free(places);
    }

    // Code lens over Pawn.cs: `Pawn` and `Health` are named once in Use.cs,
    // `Hit` never.
    RlnLenses lenses = {0};
    status = rln_code_lens(session, pawn_path, NULL, &lenses);
    CHECK(status == RLN_OK, "code lens should come back, got %d", status);
    if (status == RLN_OK) {
        CHECK(lenses.count == 3, "a type, a field and a method, got %zu", lenses.count);
        if (lenses.count == 3) {
            CHECK(lenses.items[0].count == 1, "Pawn is used once, got %u", lenses.items[0].count);
            CHECK(lenses.items[1].count == 1, "Health is used once, got %u",
                  lenses.items[1].count);
            CHECK(lenses.items[2].count == 0, "Hit is unused, got %u", lenses.items[2].count);
        }
        rln_lenses_free(lenses);
    }

    check_completion_items(session, use_path);
    check_rename(session, use_path, use_text, offset);

    check_navigation(session, pawn_path, use_path, use_text);

    check_insight(session, use_path, use_text);
    check_configured(session, directory, use_path);

    // A refusal, and the reason behind it.
    RlnLocations nothing = {0};
    CHECK(rln_definition(session, use_path, 0, &nothing) == RLN_NOT_A_NAME,
          "offset zero is the `namespace` keyword");
    RlnString message = rln_last_error(session);
    CHECK(message.length > 0, "there should be a reason to show");
    rln_text_free(message);

    // Nulls, which a caller will pass eventually.
    CHECK(rln_open(session, NULL) == RLN_BAD_ARGUMENT, "a null path is refused");
    CHECK(rln_open(NULL, use_path) == RLN_BAD_ARGUMENT, "a null session is refused");
    rln_close(NULL, NULL);

    rln_close(session, use_path);
    rln_session_free(session);
    rln_session_free(NULL);
}

// MARK: - syntax-level editing: formatting, structure, braces, comments

static RlnEdits no_edits(void) {
    RlnEdits edits = {NULL, 0, NULL, 0, NULL, 0};
    return edits;
}

static void check_editing(const char *directory) {
    printf("editing\n");

    CHECK(sizeof(RlnFoldingRange) == 28, "RlnFoldingRange is %zu bytes", sizeof(RlnFoldingRange));
    CHECK(sizeof(RlnBracePair) == 20, "RlnBracePair is %zu bytes", sizeof(RlnBracePair));
    CHECK(sizeof(RlnSnippet) == sizeof(RlnEdits) + 8, "RlnSnippet is %zu bytes", sizeof(RlnSnippet));
    CHECK(rln_fold_kind_count() == RLN_FOLD_NONSTRUCTURAL + 1,
          "the library knows %u fold kinds, this header %u", rln_fold_kind_count(),
          RLN_FOLD_NONSTRUCTURAL + 1);

    char path[1024];
    snprintf(path, sizeof path, "%s/Format.cs", directory);
    const char *text = "class C {\nint x=1;\n    ///\n    int M(int a) { return a; }\n}\n";
    write_file(path, text);

    RlnSession *session = rln_session_new(directory, NULL, NULL, 0);
    CHECK(session != NULL, "the session should open");
    if (session == NULL) {
        return;
    }

    // No compilation, not even an open file: the saved text is enough.
    RlnEdits edits = no_edits();
    RlnStatus status = rln_format_document(session, path, NULL, &edits);
    CHECK(status == RLN_OK, "it should format, got %d", status);
    if (status == RLN_OK) {
        CHECK(edits.count >= 3, "the brace, the indentation and `=`, got %zu", edits.count);
        rln_edits_free(edits);
    }
    edits = no_edits();
    status = rln_format_range(session, path, text, 0, 1, &edits);
    CHECK(status == RLN_OK && edits.count == 1, "only the first line's brace, got %zu", edits.count);
    if (status == RLN_OK) {
        rln_edits_free(edits);
    }
    edits = no_edits();
    uint32_t semicolon = (uint32_t)(strstr(text, "=1;") - text) + 3;
    status = rln_format_on_type(session, path, text, semicolon, ';', &edits);
    CHECK(status == RLN_OK && edits.count >= 1, "typing `;` formats the field");
    if (status == RLN_OK) {
        rln_edits_free(edits);
    }

    RlnString indentation = {0};
    status = rln_indentation_for_new_line(session, path, text, 9, &indentation);
    CHECK(status == RLN_OK && indentation.bytes != NULL && indentation.length == 4,
          "a new line after `{` is one level in");
    if (status == RLN_OK) {
        rln_text_free(indentation);
    }

    RlnFoldingRanges folds = {0};
    status = rln_block_structure(session, path, text, false, &folds);
    CHECK(status == RLN_OK, "it should fold, got %d", status);
    if (status == RLN_OK) {
        CHECK(folds.count == 1, "the class, got %zu", folds.count);
        if (folds.count > 0) {
            char banner[64];
            read_text(folds.strings, folds.items[0].banner, banner, sizeof banner);
            CHECK(strcmp(banner, "...") == 0, "the banner was %s", banner);
            CHECK(folds.items[0].kind == RLN_FOLD_TYPE, "a type");
            CHECK(folds.items[0].start == 7, "folded from after `class C`");
        }
        rln_folding_ranges_free(folds);
    }

    RlnBracePair pair = {0};
    status = rln_brace_match(session, path, text, 8, &pair);
    CHECK(status == RLN_OK && pair.found, "the class's brace should match");
    CHECK(pair.close_start == (uint32_t)(strrchr(text, '}') - text), "with the last brace");

    RlnSnippet snippet = {0};
    uint32_t slashes = (uint32_t)(strstr(text, "///") - text) + 3;
    status = rln_doc_comment_on_typed(session, path, text, slashes, &snippet);
    CHECK(status == RLN_OK && snippet.found, "`///` above M should expand");
    if (status == RLN_OK) {
        CHECK(snippet.edits.count == 1, "one edit, got %zu", snippet.edits.count);
        if (snippet.edits.count == 1) {
            char written[512];
            read_text(snippet.edits.strings, snippet.edits.items[0].text, written, sizeof written);
            CHECK(strstr(written, "<param name=\"a\"></param>") != NULL, "wrote %s", written);
            CHECK(strstr(written, "<returns></returns>") != NULL, "wrote %s", written);
        }
        rln_snippet_free(snippet);
    }
    snippet = (RlnSnippet){0};
    status = rln_doc_comment_on_enter(session, path, text, 0, &snippet);
    CHECK(status == RLN_OK && !snippet.found, "Enter on the first line writes nothing");
    if (status == RLN_OK) {
        rln_snippet_free(snippet);
    }
    snippet = (RlnSnippet){0};
    status = rln_insert_doc_comment(session, path, text, 2, &snippet);
    CHECK(status == RLN_OK && snippet.found, "the class can be documented");
    if (status == RLN_OK) {
        rln_snippet_free(snippet);
    }

    edits = no_edits();
    status = rln_toggle_line_comment(session, path, text, 0, 0, &edits);
    CHECK(status == RLN_OK && edits.count == 1, "one line, one `//`");
    if (status == RLN_OK) {
        rln_edits_free(edits);
    }
    edits = no_edits();
    status = rln_toggle_block_comment(session, path, text, 0, 5, &edits);
    CHECK(status == RLN_OK && edits.count == 2, "a `/*` and a `*/`");
    if (status == RLN_OK) {
        rln_edits_free(edits);
    }

    CHECK(rln_format_document(session, NULL, NULL, &edits) == RLN_BAD_ARGUMENT,
          "a null path is refused");
    rln_session_free(session);
}

// MARK: - refactoring dialogs

/// Whether any edit of `result` writes `needle`.
static int writes(const RlnRefactorResult *result, const char *needle) {
    char text[4096];
    for (size_t index = 0; index < result->edits.count; index += 1) {
        read_text(result->edits.strings, result->edits.items[index].text, text, sizeof text);
        if (strstr(text, needle) != NULL) {
            return 1;
        }
    }
    return 0;
}

/// Each dialog's refactoring on a project of its own: what the dialogs list,
/// and one run of each with choices made.
static void check_refactoring_dialogs(const char *directory) {
    printf("refactoring dialogs\n");
    CHECK(sizeof(RlnChangeParam) == 40, "RlnChangeParam is %zu bytes", sizeof(RlnChangeParam));
    CHECK(sizeof(RlnMemberChoice) == 16, "RlnMemberChoice is %zu bytes", sizeof(RlnMemberChoice));
    CHECK(sizeof(RlnRefactorResult) == 56, "RlnRefactorResult is %zu bytes",
          sizeof(RlnRefactorResult));
    CHECK(sizeof(RlnSignatureParameter) == 36, "RlnSignatureParameter is %zu bytes",
          sizeof(RlnSignatureParameter));
    CHECK(sizeof(RlnSignatureInfo) == 56, "RlnSignatureInfo is %zu bytes",
          sizeof(RlnSignatureInfo));
    CHECK(sizeof(RlnDialogMember) == 20, "RlnDialogMember is %zu bytes", sizeof(RlnDialogMember));
    CHECK(sizeof(RlnDialogMembers) == 64, "RlnDialogMembers is %zu bytes",
          sizeof(RlnDialogMembers));
    CHECK(RLN_DIALOG_MOVE_STATIC_MEMBERS == 4, "the dialog kinds moved");

    char shop_path[1024], client_path[1024];
    snprintf(shop_path, sizeof shop_path, "%s/Shop.cs", directory);
    snprintf(client_path, sizeof client_path, "%s/Client.cs", directory);
    const char *shop_text =
        "namespace Store;\n"
        "public class Stock { public virtual int Count() => 0; }\n"
        "public class Shop : Stock\n"
        "{\n"
        "    public void Buy(string item, int count) { }\n"
        "    public int Total { get; set; }\n"
        "    public static int Tax(int amount) => amount / 10;\n"
        "}\n";
    write_file(shop_path, shop_text);
    write_file(client_path,
               "namespace Store;\n"
               "public class Client { void Visit(Shop shop) { shop.Buy(\"pen\", 2); } }\n");

    RlnSession *session = rln_session_new(directory, NULL, NULL, 0);
    CHECK(session != NULL, "the session should open");
    if (session == NULL) {
        return;
    }
    const char *paths[2] = {shop_path, client_path};
    CHECK(rln_compile(session, paths, 2, NULL) == RLN_OK, "the shop should compile");
    uint32_t buy = (uint32_t)(strstr(shop_text, "Buy") - shop_text);
    uint32_t shop = (uint32_t)(strstr(shop_text, "Shop :") - shop_text);
    uint32_t tax = (uint32_t)(strstr(shop_text, "Tax") - shop_text);
    char text[256];

    RlnSignatureInfo info = {0};
    RlnStatus status = rln_signature_info(session, shop_path, NULL, buy, &info);
    CHECK(status == RLN_OK && info.refused.length == 0 && info.parameter_count == 2,
          "Buy has two parameters");
    if (status == RLN_OK) {
        if (info.parameter_count == 2) {
            read_text(info.strings, info.parameters[1].name, text, sizeof text);
            CHECK(strcmp(text, "count") == 0, "the second is count, was %s", text);
        }
        rln_signature_info_free(info);
    }

    RlnRefactorResult result = {0};
    RlnChangeParam order[3] = {
        {1, NULL, NULL, NULL, NULL},
        {0, NULL, NULL, NULL, NULL},
        {-1, "bool", "gift", "false", NULL},
    };
    status = rln_change_signature(session, shop_path, NULL, buy, order, 3, &result);
    CHECK(status == RLN_OK && result.refused.length == 0, "the signature changes");
    if (status == RLN_OK) {
        CHECK(writes(&result, "int count, string item, bool gift = false"),
              "the declaration is reordered");
        CHECK(writes(&result, "2, \"pen\""), "and the call in the other file");
        rln_refactor_result_free(result);
    }
    RlnChangeParam twice[2] = {{0, NULL, NULL, NULL, NULL}, {0, NULL, NULL, NULL, NULL}};
    status = rln_change_signature(session, shop_path, NULL, buy, twice, 2, &result);
    CHECK(status == RLN_OK && result.refused.length > 0 && result.edits.count == 0,
          "a parameter twice is refused, with a reason");
    if (status == RLN_OK) {
        rln_refactor_result_free(result);
    }

    RlnDialogMembers listed = {0};
    status = rln_dialog_members(session, shop_path, NULL, shop, RLN_DIALOG_EXTRACT_INTERFACE,
                                &listed);
    CHECK(status == RLN_OK && listed.member_count == 2, "Buy and Total can go in an interface");
    if (status == RLN_OK) {
        read_text(listed.strings, listed.suggested_name, text, sizeof text);
        CHECK(strcmp(text, "IShop") == 0, "the suggested name was %s", text);
        rln_dialog_members_free(listed);
    }
    status = rln_dialog_members(session, shop_path, NULL, shop, RLN_DIALOG_PULL_MEMBERS_UP,
                                &listed);
    CHECK(status == RLN_OK, "pull members up lists");
    if (status == RLN_OK) {
        read_text(listed.strings, listed.destinations, text, sizeof text);
        CHECK(strcmp(text, "Stock") == 0, "the destination was %s", text);
        rln_dialog_members_free(listed);
    }

    const char *members[2] = {"Buy", "Total"};
    status = rln_extract_interface(session, shop_path, NULL, shop, "IShop", members, 2, 1, &result);
    CHECK(status == RLN_OK && result.refused.length == 0, "an interface is extracted");
    if (status == RLN_OK) {
        CHECK(writes(&result, "public interface IShop"), "into a file of its own");
        rln_refactor_result_free(result);
    }

    RlnMemberChoice total = {"Total", 0};
    status = rln_extract_base_class(session, shop_path, NULL, shop, "ShopBase", &total, 1, 0, &result);
    CHECK(status == RLN_OK && result.refused.length == 0 && writes(&result, "class ShopBase : Stock"),
          "a base class is extracted between Shop and Stock");
    if (status == RLN_OK) {
        rln_refactor_result_free(result);
    }

    status = rln_pull_members_up(session, shop_path, NULL, shop, "Stock", &total, 1, &result);
    CHECK(status == RLN_OK && result.refused.length == 0 && writes(&result, "Total"),
          "Total is pulled up to Stock");
    if (status == RLN_OK) {
        rln_refactor_result_free(result);
    }

    const char *count[1] = {"Count()"};
    status = rln_generate_overrides(session, shop_path, NULL, shop, count, 1, &result);
    CHECK(status == RLN_OK && writes(&result, "public override int Count()"),
          "Count is overridden");
    if (status == RLN_OK) {
        rln_refactor_result_free(result);
    }

    const char *statics[1] = {"Tax"};
    status = rln_move_static_members(session, shop_path, NULL, tax, "Taxes", statics, 1, 1, &result);
    CHECK(status == RLN_OK && writes(&result, "public static class Taxes"),
          "Tax moves to a new static class");
    if (status == RLN_OK) {
        rln_refactor_result_free(result);
    }

    CHECK(rln_extract_interface(session, NULL, NULL, 0, "I", members, 2, 0, &result) ==
              RLN_BAD_ARGUMENT,
          "a null path is refused");
    rln_session_free(session);
}

int main(int argc, char **argv) {
    const char *directory = argc > 1 ? argv[1] : ".";
    printf("checking rustlyn.h against the library it describes\n");
    check_layout();
    check_calls(directory);
    check_editing(directory);
    check_refactoring_dialogs(directory);
    if (failures == 0) {
        printf("ok\n");
        return 0;
    }
    printf("%d check(s) failed\n", failures);
    return 1;
}
