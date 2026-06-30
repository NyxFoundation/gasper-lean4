import ProofWidgets.Component.HtmlDisplay


namespace GasperBeaconChain.Visualizations.Theme

open ProofWidgets Lean


def canvasBg  : String := "#0e1320"
def panelBg   : String := "#161c2c"
def ink       : String := "#e9eef5"
def sub       : String := "#9aa7bd"
def grid      : String := "#2a3346"
def blue      : String := "#58c4dd"
def blueDeep  : String := "#3aa0ff"
def green     : String := "#83c167"
def red       : String := "#fc6255"
def gold      : String := "#f0ac5f"
def purple    : String := "#b18bd0"
def teal      : String := "#5cd0b3"
def slate     : String := "#7b8aa6"


@[inline] def s (str : String) : Json := Json.str str
@[inline] def n (x : Float) : Json := toJson x

def css (pairs : List (String × String)) : Json :=
  Json.mkObj (pairs.map (fun (k, v) => (k, Json.str v)))

@[inline] def el (tag : String) (attrs : Array (String × Json)) (cs : Array Html := #[]) : Html :=
  .element tag attrs cs


def text (x y : Float) (str : String) (size : Float := 14) (color : String := ink)
    (anchor : String := "middle") (weight : String := "500") : Html :=
  el "text" #[("x", n x), ("y", n y), ("textAnchor", s anchor),
      ("fontFamily", s "ui-monospace, SFMono-Regular, Menlo, monospace"),
      ("fontSize", n size), ("fontWeight", s weight), ("fill", s color)] #[.text str]

def line (x1 y1 x2 y2 : Float) (color : String) (w : Float := 2) (dash : String := "")
    (cap : String := "round") : Html :=
  el "line" (#[("x1", n x1), ("y1", n y1), ("x2", n x2), ("y2", n y2),
      ("stroke", s color), ("strokeWidth", n w), ("strokeLinecap", s cap)]
    ++ (if dash == "" then #[] else #[("strokeDasharray", s dash)]))

def rect (x y w h : Float) (fill : String) (rx : Float := 0) (opacity : Float := 1)
    (stroke : String := "") (sw : Float := 0) : Html :=
  el "rect" (#[("x", n x), ("y", n y), ("width", n w), ("height", n h), ("fill", s fill),
      ("rx", n rx), ("fillOpacity", n opacity)]
    ++ (if stroke == "" then #[] else #[("stroke", s stroke), ("strokeWidth", n sw)]))

def circle (cx cy r : Float) (fill : String) (opacity : Float := 1)
    (stroke : String := "") (sw : Float := 0) : Html :=
  el "circle" (#[("cx", n cx), ("cy", n cy), ("r", n r), ("fill", s fill),
      ("fillOpacity", n opacity)]
    ++ (if stroke == "" then #[] else #[("stroke", s stroke), ("strokeWidth", n sw)]))

def path (d : String) (stroke : String) (w : Float := 2) (fill : String := "none")
    (dash : String := "") (marker : String := "") : Html :=
  el "path" (#[("d", s d), ("stroke", s stroke), ("strokeWidth", n w), ("fill", s fill),
      ("strokeLinecap", s "round")]
    ++ (if dash == "" then #[] else #[("strokeDasharray", s dash)])
    ++ (if marker == "" then #[] else #[("markerEnd", s s!"url(#{marker})")]))

def arrowDefs (id : String) (color : String) : Html :=
  el "defs" #[] #[
    el "marker" #[("id", s id), ("markerWidth", n 9), ("markerHeight", n 9),
        ("refX", n 7), ("refY", n 3), ("orient", s "auto"), ("markerUnits", s "userSpaceOnUse")]
      #[el "path" #[("d", s "M0,0 L7,3 L0,6 Z"), ("fill", s color)]]]

@[inline] def group (cs : Array Html) : Html := el "g" #[] cs

def svg (width height : Float) (body : Array Html) : Html :=
  el "svg" #[("width", n width), ("height", n height), ("viewBox", s s!"0 0 {width} {height}"),
      ("style", css [("display", "block"), ("borderRadius", "10px")])]
    (#[rect 0 0 width height canvasBg 10] ++ body)


def figure (title subtitle : String) (body : Html) (caption : String := "") : Html :=
  el "div" #[("style", css [
      ("background", panelBg), ("padding", "16px 18px 14px"), ("borderRadius", "14px"),
      ("fontFamily", "ui-monospace, SFMono-Regular, Menlo, monospace"), ("color", ink),
      ("maxWidth", "fit-content"), ("boxShadow", "0 1px 0 #ffffff10 inset")])]
    (#[ el "div" #[("style", css [("fontSize", "16px"), ("fontWeight", "650"),
            ("letterSpacing", "0.2px")])] #[.text title],
        el "div" #[("style", css [("fontSize", "12px"), ("color", sub), ("margin", "3px 0 12px")])]
          #[.text subtitle],
        body ]
    ++ (if caption == "" then #[] else
        #[el "div" #[("style", css [("fontSize", "12px"), ("color", sub), ("marginTop", "12px"),
            ("lineHeight", "1.5"), ("maxWidth", "640px")])] #[.text caption]]))

def row (gap : Float) (items : Array Html) : Html :=
  el "div" #[("style", css [("display", "flex"), ("alignItems", "center"),
      ("gap", s!"{gap}px"), ("flexWrap", "wrap")])] items

def col (gap : Float) (items : Array Html) : Html :=
  el "div" #[("style", css [("display", "flex"), ("flexDirection", "column"),
      ("gap", s!"{gap}px")])] items

def pill (label color : String) (textColor : String := "#0e1320") : Html :=
  el "span" #[("style", css [("background", color), ("color", textColor),
      ("padding", "2px 9px"), ("borderRadius", "999px"), ("fontSize", "12px"),
      ("fontWeight", "600"), ("whiteSpace", "nowrap")])] #[.text label]

def card (accent : String) (children : Array Html) : Html :=
  el "div" #[("style", css [("background", "#1b2233"), ("borderLeft", s!"4px solid {accent}"),
      ("borderRadius", "10px"), ("padding", "11px 14px"), ("minWidth", "520px")])] children

def verdict (label : String) (b : Bool) : Html :=
  pill s!"{label} = {b}" (if b then green else red)

end GasperBeaconChain.Visualizations.Theme
