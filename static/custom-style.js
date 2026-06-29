// ===========================================================================
//  #explode の Fitch 表の整形(DOM 保持・ホバー維持・桁揃え)
// ===========================================================================
//
//  literate モードの `#explode` 出力は core の `Highlighted.Message.blockHtml`
//  により `<pre class="hl lean lean-output {severity}">` として描画される。
//  この <pre> には、表の骨組み(text ノード:`0│ │ ∀I │` や Fitch の罫線)と、
//  ハイライトされた型(`<span class="highlighted">` … ホバー付き)が混在する。
//
//  SubVerso はメッセージを幅 ~120 で再整形して取り込むため、
//    (1) 長い行に「継続改行(ハード改行)」が埋め込まれて表が分断され、
//    (2) その再整形で列の padding(空白)が崩れて桁がずれる。
//  どちらも CSS では直せないので、描画後にこの 2 パスで補正する:
//
//    パス1(dewrap): 継続改行 + 再インデントを 1 個の空白へ畳み、各行を 1 行へ。
//    パス2(realign): 各行の最初の 3 本の `│`(Step│Hyp│Ref│)を全行で揃える。
//                    列ごとに「内容の最大幅」へ trailing space を調整する
//                    (= explode 本来の桁幅を再構成)。
//
//  いずれの編集も、対象は `│`(U+2502)を含む `.lean-output` の <pre> に限定。
//  さらに編集するのは **空白(padding)の text ノードだけ** で、型やトークンの
//  span(ホバー source)は一切書き換えない。`textContent` も使わないので、
//  ハイライトとホバーは保持される。通常コードブロック(<code class="hl lean
//  block">)や数式(<code class="math …">)は `.lean-output` ではないため対象外。
// ===========================================================================

(function () {
  "use strict";

  // 行頭が「ステップ番号 + 縦罫線」かどうか(表の新しいステップ行の判定)。
  const ROW_START = /^\s*\d+\s*│/;
  const BAR = "│"; // U+2502

  // <pre> 配下の text ノードを文書順に集め、連結文字列とオフセットを返す。
  function collect(pre) {
    const walker = document.createTreeWalker(pre, NodeFilter.SHOW_TEXT, null);
    const nodes = [];
    const starts = [];
    let full = "";
    let node;
    while ((node = walker.nextNode())) {
      starts.push(full.length);
      nodes.push(node);
      full += node.data;
    }
    return { nodes, starts, full };
  }

  // 連結文字列に対する編集([start,end) を repl で置換、start==end は挿入)を、
  // 元の text ノード群へ適用する。編集は start の降順で渡す前提(後ろから適用し
  // オフセットのずれを避ける)。編集範囲は常に空白なので span は壊れない。
  function applyEdits(nodes, starts, edits) {
    for (const edit of edits) {
      if (edit.start === edit.end) {
        // 挿入: start を含む(または start で始まる)text ノードを探す。
        for (let i = 0; i < nodes.length; i++) {
          const ns = starts[i];
          const ne = ns + nodes[i].data.length;
          if ((ns <= edit.start && edit.start < ne) ||
              (edit.start === ne && i === nodes.length - 1)) {
            const a = edit.start - ns;
            nodes[i].data = nodes[i].data.slice(0, a) + edit.repl + nodes[i].data.slice(a);
            break;
          }
        }
      } else {
        // 置換: 範囲に重なる text ノードを書き換える(複数ノード跨ぎにも対応)。
        let placed = false;
        for (let i = 0; i < nodes.length; i++) {
          const ns = starts[i];
          const ne = ns + nodes[i].data.length;
          if (ne <= edit.start || ns >= edit.end) continue; // 重なりなし
          const a = Math.max(0, edit.start - ns);
          const b = Math.min(nodes[i].data.length, edit.end - ns);
          const insert = placed ? "" : edit.repl;
          placed = true;
          nodes[i].data = nodes[i].data.slice(0, a) + insert + nodes[i].data.slice(b);
        }
      }
    }
  }

  // パス1: 継続改行を検出して「改行 + 再インデント空白 → 空白 1 個」へ畳む編集。
  function dewrapEdits(full) {
    const edits = [];
    let pos = 0;
    while (true) {
      const nl = full.indexOf("\n", pos);
      if (nl === -1) break;
      let nextEnd = full.indexOf("\n", nl + 1);
      if (nextEnd === -1) nextEnd = full.length;
      const nextLine = full.slice(nl + 1, nextEnd);
      // 次行が「新しいステップ行」でも「空行」でもなければ、継続行とみなす。
      if (!ROW_START.test(nextLine) && nextLine.trim() !== "") {
        const lead = nextLine.length - nextLine.trimStart().length;
        edits.push({ start: nl, end: nl + 1 + lead, repl: " " });
      }
      pos = nl + 1;
    }
    edits.reverse(); // start 降順
    return edits;
  }

  // パス2: 各 Fitch 行の最初の 3 本の `│` を全行で揃える編集。
  // 列ごとに内容(trailing space を除いた幅)の最大値を求め、各行の trailing
  // space をその幅へ調整する。これは explode 本来の桁揃え(padRight)の再構成。
  function repadEdits(full) {
    // 行と、各行の最初の 3 本の `│` のグローバル位置を集める。
    const rows = [];
    let pos = 0;
    while (pos <= full.length) {
      let nl = full.indexOf("\n", pos);
      if (nl === -1) nl = full.length;
      const line = full.slice(pos, nl);
      if (ROW_START.test(line)) {
        const b1 = full.indexOf(BAR, pos);
        const b2 = b1 === -1 ? -1 : full.indexOf(BAR, b1 + 1);
        const b3 = b2 === -1 ? -1 : full.indexOf(BAR, b2 + 1);
        if (b1 !== -1 && b2 !== -1 && b3 !== -1 && b3 < nl) {
          // 各列の開始位置(s)と終了 `│` 位置(b)。
          rows.push({
            seg: [
              { s: pos, b: b1 },     // Step
              { s: b1 + 1, b: b2 },  // Hyp
              { s: b2 + 1, b: b3 },  // Ref
            ],
          });
        }
      }
      if (nl === full.length) break;
      pos = nl + 1;
    }
    if (rows.length === 0) return [];

    // 列ごとの内容幅(trailing space を除く)。
    const contentLen = (s, b) => {
      let e = b;
      while (e > s && full[e - 1] === " ") e--;
      return e - s;
    };
    const maxLen = [0, 0, 0];
    for (const r of rows) {
      for (let k = 0; k < 3; k++) {
        maxLen[k] = Math.max(maxLen[k], contentLen(r.seg[k].s, r.seg[k].b));
      }
    }

    // 各行・各列の trailing space を「最大内容幅まで」に揃える編集を作る。
    const edits = [];
    for (const r of rows) {
      for (let k = 0; k < 3; k++) {
        const { s, b } = r.seg[k];
        const cl = contentLen(s, b);
        const want = maxLen[k] - cl;        // 望ましい trailing space 数
        const contentEnd = s + cl;          // 内容直後(ここから `│` までは空白)
        // [contentEnd, b) の空白を want 個の空白へ置換(want 個でも no-op で安全)。
        edits.push({ start: contentEnd, end: b, repl: " ".repeat(want) });
      }
    }
    // start 降順に適用してオフセットのずれを防ぐ。
    edits.sort((x, y) => y.start - x.start);
    return edits;
  }

  function process(pre) {
    if (pre.dataset.explodeDewrapped === "1") return;
    let info = collect(pre);
    // Fitch 表(縦罫線を含む)以外は対象外 → #explode 以外の出力には触れない。
    if (info.full.indexOf(BAR) === -1) return;

    pre.dataset.explodeDewrapped = "1";
    pre.classList.add("explode-output");

    // パス1: 継続改行の除去(各行を 1 行に戻す)。
    applyEdits(info.nodes, info.starts, dewrapEdits(info.full));

    // パス2: dewrap 後の状態で列を再パディングして桁を揃える。
    info = collect(pre);
    applyEdits(info.nodes, info.starts, repadEdits(info.full));
  }

  function run() {
    document
      .querySelectorAll("pre.lean-output, .code-box .lean-output")
      .forEach(process);
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", run);
  } else {
    run();
  }
})();
