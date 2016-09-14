const cssPath = "node_modules/w2ui/"

const afterChangeSubject = new Rx.Subject<{}>()
export const afterChange$ = afterChangeSubject.asObservable()
export const errorUnderlineClass = "theme_error_underline"

interface Theme {
  aceTheme: string
  background: string
  contextDivider: string
  css: string
  errorUnderlineStyle: string
  foreground: string
  goalStroke: string
  linkStroke: string
  processed: string
  processing: string
  highlight: string
  separatorColor: string
  svgBackground: string
  syntaxComment: string
  syntaxGallina: string
  syntaxKeyword: string
  syntaxNotation: string
  syntaxTactic: string
  syntaxTerminator: string
  syntaxVariable: string
  syntaxVernacular: string
  toprocess: string
  tacticFill: string
}

namespace BrightTheme {
  export const aceTheme = ""
  export const background = "rgba(255, 255, 255, 1)"
  export const css = `${cssPath}/w2ui.min.css`
  export const contextDivider = "1px solid black"
  export const errorUnderlineStyle = "2px dotted red"
  export const foreground = "black"
  export const goalStroke = "black"
  export const linkStroke = "black"
  export const processed = "rgba(144, 238, 144, 1)"
  export const processing = "rgba(255, 179, 71, 1)"
  export const highlight = "deepskyblue"
  export const separatorColor = "#999999"
  export const svgBackground = "white"
  export const syntaxComment = "rgb(165, 42, 42)"
  export const syntaxGallina = "blue"
  export const syntaxKeyword = "red"
  export const syntaxNotation = "brown"
  export const syntaxTactic = "rgb(147, 112, 219)"
  export const syntaxTerminator = "red"
  export const syntaxVariable = "rgb(147, 112, 219)"
  export const syntaxVernacular = "rgb(255, 69, 0)"
  export const toprocess = "rgba(173, 216, 230, 1)"
  export const tacticFill = "rgb(147, 112, 219)"
}

namespace DarkTheme {
  export const aceTheme = "ace/theme/monokai"
  export const background = "rgba(39, 40, 34, 1)"
  export const css = `${cssPath}/w2ui-dark.min.css`
  export const contextDivider = "1px solid white"
  export const errorUnderlineStyle = "2px dotted red"
  export const foreground = "white"
  export const goalStroke = "white"
  export const linkStroke = "white"
  export const processed = "rgba(4, 98, 4, 1)"
  export const processing = "rgba(185, 109, 01, 1)"
  export const highlight = "deepskyblue"
  export const separatorColor = "#999999"
  export const svgBackground = "black"
  export const syntaxComment = "rgb(165, 42, 42)"
  export const syntaxGallina = "lightblue"
  export const syntaxKeyword = "red"
  export const syntaxNotation = "brown"
  export const syntaxTactic = "rgb(147, 112, 219)"
  export const syntaxTerminator = "red"
  export const syntaxVariable = "rgb(147, 112, 219)"
  export const syntaxVernacular = "rgb(255, 69, 0)"
  export const toprocess = "rgba(73, 116, 130, 1)"
  export const tacticFill = "rgb(147, 112, 219)"
}

export let theme: Theme = BrightTheme

export function switchTo(doc: ICoqDocument, t: Theme): void {
  theme = t
  update(doc)
}

export function switchToBright(doc: ICoqDocument): void { switchTo(doc, BrightTheme) }

export function switchToDark(doc: ICoqDocument): void { switchTo(doc, DarkTheme) }

function update(doc: ICoqDocument): void {

  jss.set(".w2ui-layout>div .w2ui-resizer", {
    "background-color": "transparent"
  })
  jss.set("body", { "color": theme.foreground })
  jss.set(".w2ui-layout > div .w2ui-panel .w2ui-panel-tabs", {
    "background-color": theme.background
  })
  jss.set(".w2ui-layout>div .w2ui-panel .w2ui-panel-content", {
    "background-color": theme.background,
    "color": theme.foreground,
  })
  jss.set("#pretty-content", { "background-color": theme.background })
  jss.set("#prooftree", { "background-color": theme.svgBackground })
  jss.set(".processed", { "background-color": theme.processed })
  jss.set(".processing", { "background-color": theme.processing })
  jss.set(".toprocess", { "background-color": theme.toprocess })
  jss.set(".highlight", { "background-color": theme.highlight })
  jss.set(".goal", { "fill": theme.background })
  jss.set(".tactic", { "fill": theme.tacticFill })
  jss.set(".ace_coqcomment", { "color": theme.syntaxComment })
  jss.set(".ace_gallina", { "color": theme.syntaxGallina })
  jss.set(".ace_tactic", { "color": theme.syntaxTactic })
  jss.set(".ace_terminator", { "color": theme.syntaxTerminator })
  jss.set(".ace_vernacular", { "color": theme.syntaxVernacular })
  jss.set(".tag-keyword", { "color": theme.syntaxKeyword })
  jss.set(".tag-notation", { "color": theme.syntaxNotation })
  jss.set(".tag-variable", { "color": theme.syntaxVariable })
  jss.set(".context-divider", {
    "border": "0",
    "border-top": theme.contextDivider,
    "margin": "0",
  })

  jss.set(".goal", {
    "stroke": theme.goalStroke,
    "stroke-width": "2px",
  })

  jss.set(".currentnode", {
    "stroke": "#03C03C",
    "stroke-width": "4px",
  })

  jss.set(".link", { "stroke": theme.linkStroke })

  jss.set(".w2ui-layout>div .w2ui-resizer", { "background-color": theme.separatorColor })

  jss.set("svg body", {
    "background-color": "transparent",
    "font-family": "monospace",
    "padding": "2px",
  })

  jss.set("." + errorUnderlineClass, {
    position: "absolute",
    "border-bottom": theme.errorUnderlineStyle,
  })

  doc.editor.setTheme(theme.aceTheme)
  doc.contextPanel.setTheme(theme.aceTheme)

  $.get(theme.css, (response) => {
    $("#theme").text(response)
    $("#w2uicss")
      .on("load", () => afterChangeSubject.onNext({}))
      .attr("href", theme.css)
  })

  afterChangeSubject.onNext({})
}

export function setupTheme(doc: ICoqDocument): void {
  update(doc)
}
