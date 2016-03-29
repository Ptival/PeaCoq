let cssPath = "js/lib/w2ui/";
let errorUnderlineClass = "theme_error_underline";

interface Theme {
  aceTheme: string;
  background: string;
  contextDivider: string;
  css: string;
  errorUnderlineStyle: string;
  foreground: string;
  goalStroke: string;
  linkStroke: string;
  processed: string;
  processing: string;
  separatorColor: string;
  svgBackground: string;
  syntaxComment: string;
  syntaxGallina: string;
  syntaxKeyword: string;
  syntaxNotation: string;
  syntaxTactic: string;
  syntaxTerminator: string;
  syntaxVariable: string;
  syntaxVernacular: string;
  toprocess: string;
  tacticFill: string;
}

namespace BrightTheme {
  export let aceTheme = "";
  export let background = "rgba(255, 255, 255, 1)";
  export let css = cssPath + "w2ui.min.css";
  export let contextDivider = "1px solid black";
  export let errorUnderlineStyle = "2px dotted red";
  export let foreground = "black";
  export let goalStroke = "black";
  export let linkStroke = "black";
  export let processed = "rgba(144, 238, 144, 1)";
  export let processing = "rgba(255, 179, 71, 1)";
  export let separatorColor = "#999999";
  export let svgBackground = "white";
  export let syntaxComment = "rgb(165, 42, 42)";
  export let syntaxGallina = "blue";
  export let syntaxKeyword = "red";
  export let syntaxNotation = "brown";
  export let syntaxTactic = "rgb(147, 112, 219)";
  export let syntaxTerminator = "red";
  export let syntaxVariable = "rgb(147, 112, 219)";
  export let syntaxVernacular = "rgb(255, 69, 0)";
  export let toprocess = "rgba(173, 216, 230, 1)";
  export let tacticFill = "#FFF056";
}

namespace DarkTheme {
  export let aceTheme = "ace/theme/monokai";
  export let background = "rgba(39, 40, 34, 1)";
  export let css = cssPath + "w2ui-dark.min.css";
  export let contextDivider = "1px solid white";
  export let errorUnderlineStyle = "2px dotted red";
  export let foreground = "white";
  export let goalStroke = "white";
  export let linkStroke = "white";
  export let processed = "rgba(4, 98, 4, 1)";
  export let processing = "rgba(185, 109, 01, 1)";
  export let separatorColor = "#999999";
  export let svgBackground = "black";
  export let syntaxComment = "rgb(165, 42, 42)";
  export let syntaxGallina = "lightblue";
  export let syntaxKeyword = "red";
  export let syntaxNotation = "brown";
  export let syntaxTactic = "rgb(147, 112, 219)";
  export let syntaxTerminator = "red";
  export let syntaxVariable = "rgb(147, 112, 219)";
  export let syntaxVernacular = "rgb(255, 69, 0)";
  export let toprocess = "rgba(73, 116, 130, 1)";
  export let tacticFill = "#9F9006";
}

namespace Theme {

  export let theme: Theme = DarkTheme;

  export function switchToBright(): void {
    theme = BrightTheme;
    setupTheme();
  }

  export function switchToDark(): void {
    theme = DarkTheme;
    setupTheme();
  }

  export function setupTheme() {
    $.get(theme.css, (response) => {
      $('#theme').text(response);
      onResize();
    });
    $("#w2uicss").load(onResize).attr("href", theme.css);
    jss.set(".w2ui-layout>div .w2ui-resizer", {
      "background-color": "transparent"
    })
    jss.set("body", { "color": theme.foreground });
    jss.set(".w2ui-layout > div .w2ui-panel .w2ui-panel-tabs", {
      "background-color": theme.background
    });
    jss.set(".w2ui-layout>div .w2ui-panel .w2ui-panel-content", {
      "background-color": theme.background,
      "color": theme.foreground,
    });
    jss.set("#pretty-content", { "background-color": theme.background });
    jss.set("#prooftree", { "background-color": theme.svgBackground });
    jss.set(".processed", { "background-color": theme.processed });
    jss.set(".processing", { "background-color": theme.processing });
    jss.set(".toprocess", { "background-color": theme.toprocess });
    jss.set(".goal", { "fill": theme.background });
    jss.set(".tactic", { "fill": theme.tacticFill });
    jss.set(".ace_coqcomment", { "color": theme.syntaxComment });
    jss.set(".ace_gallina", { "color": theme.syntaxGallina });
    jss.set(".ace_tactic", { "color": theme.syntaxTactic });
    jss.set(".ace_terminator", { "color": theme.syntaxTerminator });
    jss.set(".ace_vernacular", { "color": theme.syntaxVernacular });
    jss.set(".tag-keyword", { "color": theme.syntaxKeyword });
    jss.set(".tag-notation", { "color": theme.syntaxNotation });
    jss.set(".tag-variable", { "color": theme.syntaxVariable });
    jss.set(".context-divider", {
      "border": "0",
      "border-top": theme.contextDivider,
      "margin": "0",
    });

    jss.set(".goal", {
      "stroke": theme.goalStroke,
      "stroke-width": "2px",
    });

    jss.set(".currentnode", {
      "stroke": "#03C03C",
      "stroke-width": "4px",
    });

    jss.set(".link", { "stroke": theme.linkStroke });

    jss.set(".w2ui-layout>div .w2ui-resizer", { "background-color": theme.separatorColor });

    jss.set("svg body", {
      "background-color": "transparent",
      "font-family": "monospace",
      "padding": "2px",
    })

    jss.set("." + errorUnderlineClass, {
      position: "absolute",
      "border-bottom": theme.errorUnderlineStyle,
    });

    coqDocument.editor.setTheme(theme.aceTheme);
    _(allEditorTabs).each((et) => { et.setTheme(theme.aceTheme); })
  }

}
