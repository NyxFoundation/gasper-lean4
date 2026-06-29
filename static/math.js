// static/math.js
// Verso literate 出力の数式描画（三経路対応）
//
// 経路 1: Verso Doc    → <code class="math inline/display">  (ページ本文)
// 経路 2: Markdown $   → テキスト中の $...$ / $$...$$         (ツールチップ)
// 経路 3: Verso→marked → $ + <code>LaTeX</code> に分断        (ツールチップ)
//
// doc.verso := true の docstring は $`...` / $$`...` を使う。
// ページ本文では Verso が <code class="math inline/display"> を出力する（経路 1）。
// ツールチップでは SubVerso が生テキストを保存し、highlightingJs の
// marked.parse() が処理する。marked はバッククォートをコードスパンと
// 解釈するため $<code>LaTeX</code> という DOM 構造が生まれる（経路 3）。
(function () {
  "use strict";
  if (typeof katex === "undefined") return;

  // root 自身とその子孫から sel に一致する要素を集める。
  // querySelectorAll は子孫しか返さないため、Observer が要素そのもの
  // (例: highlightingJs が window.onload で replaceChild する .docstring)
  // を渡してきた場合の取りこぼしを root.matches で防ぐ。
  function collectSelfAndDesc(root, sel) {
    var out = [];
    if (root.matches && root.matches(sel)) out.push(root);
    if (root.querySelectorAll) {
      var ds = root.querySelectorAll(sel);
      for (var i = 0; i < ds.length; i++) out.push(ds[i]);
    }
    return out;
  }

  // ── 経路 1: <code class="math inline/display"> ──────────────
  function renderClassed(root) {
    var sel = ".math:is(.inline,.display):not(.katex-rendered)";
    var targets = collectSelfAndDesc(root, sel);
    for (var i = 0; i < targets.length; i++) {
      var m = targets[i];
      try {
        katex.render(m.textContent, m, {
          throwOnError: false,
          displayMode: m.classList.contains("display"),
        });
      } catch (_) {
        /* 想定外の例外でも残りの数式描画は続行する(経路2/3 と同じ方針) */
      }
      m.classList.add("katex-rendered");
    }
  }

  // ── 経路 3: $ + <code>LaTeX</code> (Verso 構文が marked で分断)──
  // marked.parse() が $`...` を $ + <code>...</code> に変換した構造を検出。
  // テキストノード走査より先に実行する（経路 2 と干渉しないよう）。
  function renderVersoThroughMarked(el) {
    // 子ノードを配列にコピー（DOM 変更安全）
    var children = [];
    var child = el.firstChild;
    while (child) {
      children.push(child);
      child = child.nextSibling;
    }

    for (var i = 0; i < children.length; i++) {
      var node = children[i];

      // 再帰: 要素ノードの中も走査（ただし code/pre/katex/SVG は飛ばす）。
      // SVG(描画済み mermaid/rawsvg 図)に降りると、SVG 内へ HTML を差し込んで
      // 図を破壊し得るため、SVG 名前空間の部分木は明示的に除外する。
      if (node.nodeType === 1) {
        var tag = node.tagName;
        if (
          node.namespaceURI !== "http://www.w3.org/2000/svg" &&
          tag !== "CODE" &&
          tag !== "PRE" &&
          tag !== "SCRIPT" &&
          tag !== "STYLE" &&
          !node.classList.contains("katex")
        ) {
          renderVersoThroughMarked(node);
        }
        continue;
      }
      if (node.nodeType !== 3) continue; // テキストノード以外はスキップ

      var text = node.nodeValue;
      if (!text) continue;

      // テキスト末尾の $$ または $ を検出し、次の兄弟が <code> かを確認
      var next = node.nextSibling;
      if (!next || next.nodeType !== 1 || next.tagName !== "CODE") continue;
      // <code> が既に katex クラスを持つ場合はスキップ
      if (
        next.classList.contains("katex") ||
        next.classList.contains("katex-rendered")
      )
        continue;

      var display = false;
      var trimmed;
      if (text.length >= 2 && text.slice(-2) === "$$") {
        display = true;
        trimmed = text.slice(0, -2);
      } else if (text.length >= 1 && text.slice(-1) === "$") {
        trimmed = text.slice(0, -1);
      } else {
        continue;
      }

      // <code> の中身を数式として描画
      var latex = next.textContent;
      if (!latex) continue;

      var span = document.createElement("span");
      try {
        katex.render(latex, span, {
          throwOnError: false,
          displayMode: display,
        });
      } catch (_) {
        continue; // 描画失敗時は元のまま残す
      }

      // テキストノードを短縮し、<code> を KaTeX 出力で置換
      node.nodeValue = trimmed;
      next.parentNode.replaceChild(span, next);
    }
  }

  // ── 経路 2: テキスト中の $...$ / $$...$$ ────────────────────
  // O(n) 線形スキャナ（バックトラッキングなし）
  function scanDelimiters(text) {
    var segs = [];
    var i = 0,
      start = 0,
      n = text.length;
    while (i < n) {
      if (text[i] === "\\" && i + 1 < n && text[i + 1] === "$") {
        i += 2;
        continue;
      }
      if (text[i] !== "$") {
        i++;
        continue;
      }

      // display math $$...$$
      if (i + 1 < n && text[i + 1] === "$") {
        var cl = text.indexOf("$$", i + 2);
        if (cl === -1 || cl === i + 2) {
          i += 2;
          continue;
        }
        if (i > start) segs.push({ t: 0, v: text.slice(start, i) });
        segs.push({ t: 2, v: text.slice(i + 2, cl) });
        i = cl + 2;
        start = i;
        continue;
      }
      // inline math $...$
      var j = i + 1,
        found = false;
      while (j < n) {
        if (text[j] === "\n") break;
        if (text[j] === "\\" && j + 1 < n && text[j + 1] === "$") {
          j += 2;
          continue;
        }
        if (text[j] === "$") {
          found = true;
          break;
        }
        j++;
      }
      if (!found || j === i + 1) {
        i++;
        continue;
      }
      if (i > start) segs.push({ t: 0, v: text.slice(start, i) });
      segs.push({ t: 1, v: text.slice(i + 1, j) });
      i = j + 1;
      start = i;
    }
    if (start < n) segs.push({ t: 0, v: text.slice(start) });
    return segs;
  }

  function replaceTextNode(textNode) {
    var text = textNode.nodeValue;
    if (!text || text.indexOf("$") === -1) return;
    var segs = scanDelimiters(text);
    if (segs.length <= 1 && (!segs[0] || segs[0].t === 0)) return;
    var frag = document.createDocumentFragment();
    for (var k = 0; k < segs.length; k++) {
      var s = segs[k];
      if (s.t === 0) {
        frag.appendChild(document.createTextNode(s.v.replace(/\\\$/g, "$")));
      } else {
        var sp = document.createElement("span");
        katex.render(s.v.replace(/\\\$/g, "$"), sp, {
          throwOnError: false,
          displayMode: s.t === 2,
        });
        frag.appendChild(sp);
      }
    }
    textNode.parentNode.replaceChild(frag, textNode);
  }

  var SKIP = { CODE: 1, PRE: 1, SCRIPT: 1, STYLE: 1 };
  function walkAndRender(node) {
    if (node.nodeType === 3) {
      replaceTextNode(node);
      return;
    }
    if (node.nodeType !== 1) return;
    // SVG(描画済み mermaid/rawsvg 図)へは降りない。renderVersoThroughMarked と
    // 同じガード(SVG 内に $…$ 様の text があっても KaTeX 注入で図を壊さない)。
    if (node.namespaceURI === "http://www.w3.org/2000/svg") return;
    if (SKIP[node.tagName] || node.classList.contains("katex")) return;
    var ch = node.firstChild,
      arr = [];
    while (ch) {
      arr.push(ch);
      ch = ch.nextSibling;
    }
    for (var i = 0; i < arr.length; i++) walkAndRender(arr[i]);
  }

  function renderDocstrings(root) {
    var els = collectSelfAndDesc(root, ".docstring:not(.katex-scanned)");
    for (var i = 0; i < els.length; i++) {
      var el = els[i];
      el.classList.add("katex-scanned");
      // 経路 3 を先に処理（$<code> を除去してから経路 2 を走らせる）
      renderVersoThroughMarked(el);
      // 経路 2: 残った $...$ パターン
      if (el.textContent.indexOf("$") !== -1) walkAndRender(el);
    }
  }

  // ── 統合 ─────────────────────────────────────────────────
  function processRoot(root) {
    renderClassed(root);
    renderDocstrings(root);
  }

  processRoot(document.body || document.documentElement);

  if (typeof MutationObserver !== "undefined") {
    new MutationObserver(function (mutations) {
      for (var i = 0; i < mutations.length; i++) {
        var added = mutations[i].addedNodes;
        for (var j = 0; j < added.length; j++) {
          var node = added[j];
          if (node.nodeType !== 1) continue;
          if (node.closest && node.closest(".katex-scanned")) continue;
          processRoot(node);
        }
      }
    }).observe(document.documentElement, { childList: true, subtree: true });
  }
})();
