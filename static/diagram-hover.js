// static/diagram-hover.js
// ============================================================================
//  Mermaid 図と Verso の「検証済みホバー/定義リンク」の橋渡し
// ============================================================================
//
//  A1(%%mermaid + render-plugins.js)で描画した図のノード/エッジのラベルが、
//  そのページに存在する Lean 識別子の名前と「完全一致」する場合、コード中の
//  その識別子と **同じツールチップ(シグネチャ/docstring)と定義リンク** を図へ
//  付与する。
//
//  Verso は全コードトークンに次を埋めている:
//    - data-verso-hover="<id>"  … -verso-docs.json[<id>] が HTML ホバー内容
//    - 親 <a href="…">          … 定義/参照リンク(definitionsAsTargets)
//  本スクリプトはこれをページから回収して図へ転写するだけで、Lean 側の追加
//  実装(A2 の expander)も Core への import も要らない。
//
//  起動経路: render-plugins.js が mermaid.run の完了後に
//    window.LeanDiagramHover.enhance(div) を呼ぶ。保険として MutationObserver
//    でも mermaid SVG の挿入を監視する。
// ============================================================================

(function () {
  "use strict";

  // -verso-docs.json は一度だけ取得(Verso のホバーも同じものを使う)。
  var docDataPromise = null;
  function getDocData() {
    if (!docDataPromise) {
      docDataPromise = fetch("-verso-docs.json")
        .then(function (r) { return r.json(); })
        .catch(function () { return {}; });
    }
    return docDataPromise;
  }

  // ページのコードトークンから { 識別子テキスト -> { hoverId, href } } を構築。
  // 同名が複数あれば最初を採用(宣言トークンが先に来ることが多い)。
  var registry = null;
  function buildRegistry() {
    if (registry) return registry;
    registry = Object.create(null);
    var toks = document.querySelectorAll(".hl.lean .token");
    for (var i = 0; i < toks.length; i++) {
      var t = toks[i];
      var text = (t.textContent || "").trim();
      if (!text || registry[text]) continue;
      var a = t.closest("a[href]");
      var hoverId = t.getAttribute("data-verso-hover");
      if (hoverId == null && !a) continue; // ホバーもリンクも無いトークンは無視
      registry[text] = { hoverId: hoverId, href: a ? a.getAttribute("href") : null };
    }
    return registry;
  }

  // Verso の content(tgt) と同じ構造のツールチップ内容を組み立てる。
  function makeTooltipContent(hoverId, docData) {
    var span = document.createElement("span");
    span.className = "hl lean";
    var info = document.createElement("span");
    info.className = "hover-info";
    info.style.display = "block";
    info.innerHTML = docData[hoverId];
    span.appendChild(info);
    // docstring を marked で描画(その後 math.js の Observer が KaTeX 化する)。
    if (typeof marked !== "undefined") {
      var ds = span.querySelectorAll("code.docstring, pre.docstring");
      for (var k = 0; k < ds.length; k++) {
        var d = ds[k];
        var rendered = document.createElement("div");
        rendered.classList.add("docstring");
        rendered.innerHTML = marked.parse(d.innerText);
        d.parentNode.replaceChild(rendered, d);
      }
    }
    return span;
  }

  function attach(labelEl, info, docData) {
    if (labelEl.dataset.leanDiagramRef === "1") return;
    labelEl.dataset.leanDiagramRef = "1";
    labelEl.classList.add("lean-diagram-ref");

    // ホバー(コード中と同一の内容)。
    if (info.hoverId != null && docData[info.hoverId] && typeof tippy !== "undefined") {
      tippy(labelEl, {
        theme: "lean",
        allowHTML: true,
        interactive: true,
        maxWidth: "none",
        // 通常は body 直下(viewer の overflow:hidden で切れない)。ただし全画面中は
        // body 配下が描画対象外で見えなくなるため、そのラベルが属する diagram-viewer
        // (= 全画面要素)へ append する。tippy は mount(show)毎に appendTo を評価する
        // ので、全画面突入後の hover にも動的に効く。
        appendTo: function () {
          return document.fullscreenElement
            ? (labelEl.closest(".diagram-viewer") || document.fullscreenElement)
            : document.body;
        },
        delay: [100, null],
        content: function () { return makeTooltipContent(info.hoverId, docData); },
      });
    }

    // 定義リンク(クリックで定義へジャンプ)。
    if (info.href) {
      labelEl.style.cursor = "pointer";
      labelEl.addEventListener("click", function (e) {
        e.preventDefault();
        window.location.href = info.href;
      });
    }
  }

  // #mermaid_explode ノードに埋め込まれた judgment(MermaidRef が前置詞除去・
  // mmTrunc 800 で整えた `rule ⊢ type`)を tippy で見せる。各ノードラベル末尾の
  // 不可視マーカー <span class="lean-explode-full">…</span> の textContent が内容
  // (mmClean 済のプレーン文字列)。可視ラベルは要約のみなので、省略分をここで回収
  // する。識別子一致ホバー(b)と違い、ラベルがページの識別子と一致しなくても出る。
  function attachFullType(labelEl, fullText) {
    if (!labelEl || labelEl.dataset.leanFullType === "1") return;
    labelEl.dataset.leanFullType = "1";
    labelEl.classList.add("lean-explode-node");
    if (typeof tippy === "undefined" || !fullText) return;
    tippy(labelEl, {
      theme: "leantype",
      allowHTML: false, // プレーン文字列のみ(注入不可)
      interactive: false,
      maxWidth: 560,
      appendTo: function () {
        return document.fullscreenElement
          ? (labelEl.closest(".diagram-viewer") || document.fullscreenElement)
          : document.body;
      },
      delay: [120, null],
      content: fullText,
    });
  }

  // 図(コンテナ)内のラベルを走査する。
  //  (a) explode ノードの完全 judgment hover(span の textContent。docData 不要)。
  //  (b) ラベルがページ上の Lean 識別子と一致すれば Verso のホバー/定義リンクを転写。
  function enhance(container) {
    if (!container || !container.querySelectorAll) return;
    // (a) explode ノードの judgment hover。
    var fulls = container.querySelectorAll(".lean-explode-full");
    for (var k = 0; k < fulls.length; k++) {
      var marker = fulls[k];
      attachFullType(marker.closest(".nodeLabel") || marker.parentNode,
        (marker.textContent || "").trim());
    }
    // (b) 識別子一致のホバー/定義リンク転写(docData + registry が必要)。
    getDocData().then(function (docData) {
      var reg = buildRegistry();
      // mermaid のノード/エッジ ラベル(HTML foreignObject)と素の <text>。
      var labels = container.querySelectorAll(".nodeLabel, .edgeLabel, text");
      for (var i = 0; i < labels.length; i++) {
        var el = labels[i];
        var text = (el.textContent || "").trim();
        if (!text) continue;
        var info = reg[text];
        if (info) attach(el, info, docData);
      }
    });
  }

  window.LeanDiagramHover = { enhance: enhance };

  // 保険: render フックを通らない経路でも mermaid SVG 挿入を捕捉する。
  if (typeof MutationObserver !== "undefined") {
    new MutationObserver(function (muts) {
      for (var i = 0; i < muts.length; i++) {
        var added = muts[i].addedNodes;
        for (var j = 0; j < added.length; j++) {
          var n = added[j];
          if (n.nodeType !== 1) continue;
          if (n.querySelector && n.querySelector("svg")) enhance(n);
        }
      }
    }).observe(document.documentElement, { childList: true, subtree: true });
  }
})();
