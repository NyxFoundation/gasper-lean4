// static/diagram-view.js
// ============================================================================
//  汎用「図ビューア」コンポーネント — zoom / pan / reset(fit) / fullscreen
// ============================================================================
//  render-plugins.js が mermaid / rawsvg を描画した後に
//    window.DiagramView.attach(diagramEl)
//  を呼ぶと、その図を toolbar 付きの操作可能なビューへ包む。
//
//  ── 設計方針 ────────────────────────────────────────────────
//   - 変形は外側 stage への CSS transform(translate + scale)。SVG の viewBox を
//     いじらないので mermaid(foreignObject ラベル)も rawsvg も同一機構で扱え、
//     getBoundingClientRect が変形を反映するため diagram-hover.js の tippy/定義
//     リンクの位置決めもそのまま正しい(座標系を二重に持たない)。
//   - 依存ゼロ(Pointer Events + Fullscreen API のみ)。
//   - ドラッグ閾値でクリック(定義ジャンプ)とパンを判別。実ドラッグ後の click は
//     capture 段で握り潰し、誤ジャンプを防ぐ。
//   - ホイールズームは Ctrl/⌘ 併用時のみ(素のホイールはページスクロールを
//     妨げない)。ボタンでも増減でき、いずれもカーソル/中心を基準に拡大する。
//   - 高さは CSS の max-height で抑え、超過分はパン/ズームで辿る(巨大図が
//     ページを縦に支配しない)。冪等(data-diagram-viewed)。
// ============================================================================
(function () {
  "use strict";

  // スケール範囲は広く取る。#mermaid_explode の巨大図(100+ ノード)は自然幅が画面の
  // 何倍にもなるため、
  //  ・MIN は小さく(全画面 contain でも s≈0.05 が要る。0.2 だと fit が頭打ちして
  //    はみ出す/縮小が効かない)、
  //  ・MAX は大きく(fit が s≈0.05 のとき MAX=8 では自然サイズの 8 倍止まりで、元々
  //    小さいノード文字を読むには絶対スケール s≳2 が要る。個々のノードまで寄れるよう
  //    上限を引き上げる)。
  var MIN = 0.01;    // 最小スケール
  var MAX = 40;      // 最大スケール(巨大図の 1 ノードまで寄れる絶対倍率)
  var STEP = 1.25;   // ボタン/ホイール 1 段の倍率
  var DRAG = 4;      // クリックとパンを分ける移動量(px)

  function clamp(s) {
    return Math.max(MIN, Math.min(MAX, s));
  }

  function makeButton(glyph, title, onClick) {
    var b = document.createElement("button");
    b.type = "button";
    b.className = "diagram-btn";
    b.textContent = glyph;
    b.title = title;
    b.setAttribute("aria-label", title);
    // toolbar 操作はパン/クリック判定へ波及させない。
    b.addEventListener("click", function (e) {
      e.preventDefault();
      e.stopPropagation();
      onClick();
    });
    return b;
  }

  function attach(diagramEl) {
    if (!diagramEl || diagramEl.dataset.diagramViewed === "1") return;
    // 描画未完了(SVG 未挿入)なら何もしない。
    if (!diagramEl.querySelector("svg")) return;
    var parent = diagramEl.parentNode;
    if (!parent) return;
    diagramEl.dataset.diagramViewed = "1";

    // viewer ▷ stage ▷ diagramEl(図)。viewer は元の位置に差し込み、図を stage へ移す。
    var viewer = document.createElement("div");
    viewer.className = "diagram-viewer";
    var stage = document.createElement("div");
    stage.className = "diagram-stage";
    parent.insertBefore(viewer, diagramEl);
    stage.appendChild(diagramEl);
    viewer.appendChild(stage);

    var state = { s: 1, x: 0, y: 0 };
    // ユーザーが手動でズーム/パンしたか。resize 時に「未操作なら再 fit、操作済みなら
    // 勝手に戻さず境界だけ維持」を分けるためのフラグ。fit/reset で false に戻る。
    var userAdjusted = false;

    // ── 測定キャッシュ ──────────────────────────────────────────
    // viewer の矩形と stage の自然寸(scale=1 の幅高)を保持し、毎イベントでの
    // getBoundingClientRect(レイアウト同期 = reflow)を避ける。サイズが変わる契機
    // (リサイズ/全画面/フォント遅延ロード)でのみ ResizeObserver が更新する。
    var vw = 0, vh = 0;                  // viewer の内寸
    var viewerLeft = 0, viewerTop = 0;  // viewer の画面位置(clientX/Y → viewer 座標)
    var natW = 0, natH = 0;             // stage の自然寸(scale=1)
    var svg = stage.querySelector("svg");
    function measure() {
      var vr = viewer.getBoundingClientRect();
      vw = vr.width; vh = vr.height; viewerLeft = vr.left; viewerTop = vr.top;
      // 自然寸は「現在の transform を一時的に外して」測る(scale を含めない)。
      var prevT = stage.style.transform;
      stage.style.transform = "none";
      // mermaid は SVG に inline `max-width:<W>px` を付け、これが stage(width:
      // max-content)の幅を viewer 幅に引きずって自然寸を汚す。測定中だけ max-width を
      // 外し、SVG の本来の内在サイズ(width/height 属性 or viewBox)で natW/natH を取る。
      var prevMW = "";
      if (svg) { prevMW = svg.style.maxWidth; svg.style.maxWidth = "none"; }
      var sr = stage.getBoundingClientRect();
      natW = sr.width; natH = sr.height;
      if (svg) svg.style.maxWidth = prevMW;
      stage.style.transform = prevT;
    }

    // ── transform 適用は rAF でコアレス(1 フレーム 1 回の書き込み)──
    // ホイール連打やドラッグで state を高頻度更新しても、実際の style 書き込みと
    // それに伴う合成は次の描画フレームで一度だけ。中間状態の無駄な reflow を防ぐ。
    var raf = 0;
    function schedule() {
      if (raf) return;
      raf = requestAnimationFrame(function () {
        raf = 0;
        stage.style.transform =
          "translate(" + state.x + "px," + state.y + "px) scale(" + state.s + ")";
      });
    }

    // パン境界クランプ: 拡大時に図を viewer 外へ追い出して見失わないよう、各軸で
    // 図(stage, 幅 sw=natW·s)の位置 x を次の範囲に収める:
    //   ・図 ≤ viewer: 中央固定(ドラッグで動かさない)。
    //   ・図 > viewer: 図左端 x ∈ [EDGE−sw, vw−EDGE]
    //       (右端 x+sw ≥ EDGE で右にも図が残り、左端 x ≤ vw−EDGE で左にも残る)。
    // これが「拡大したら空白に迷子」を断つ。
    var EDGE = 48;
    function clampAxis(pos, sLen, vLen) {
      if (sLen <= vLen) return (vLen - sLen) / 2;
      return Math.min(vLen - EDGE, Math.max(EDGE - sLen, pos));
    }
    function clampPan() {
      state.x = clampAxis(state.x, natW * state.s, vw);
      state.y = clampAxis(state.y, natH * state.s, vh);
    }

    // ビューア座標 (cx,cy) を不動点に保ったまま newS へズーム。
    function zoomTo(newS, cx, cy) {
      newS = clamp(newS);
      if (newS === state.s) return;
      state.x = cx - (cx - state.x) * (newS / state.s);
      state.y = cy - (cy - state.y) * (newS / state.s);
      state.s = newS;
      userAdjusted = true;
      clampPan();
      schedule();
    }
    function viewerCenter() { return { cx: vw / 2, cy: vh / 2 }; }

    // 直近のポインタ位置(viewer 座標)。ボタン/キーのズームを「いま見ている所」を
    // 不動点に行うために使う。ポインタが図上に無い間は中央にフォールバック。
    // ドラッグ中は更新しない(パン中にフォーカスが暴れないように)。
    var lastPt = null;
    function zoomFocus() { return lastPt || viewerCenter(); }

    // fit/reset: 自然寸を測り、図を viewer に合わせる。
    //  ・通常表示: 幅にフィット(`vw/natW`、ただし自然サイズ超へは拡大しない=≤1)。
    //    explode 図は横長(depth 帯が横展開)なので幅律速で大きく見える。縦が窓を
    //    超える分はパン/ズームで辿る(横長図を contain すると幅律速で小さく潰れて
    //    しまうのを避ける)。収まる軸は中央、超える軸は先頭(左/上)寄せ。
    //  ・全画面: 幅・高さ両方に収める contain(拡大も許可、上限 MAX)+ 縦横中央。
    function fit() {
      measure();
      if (natW <= 0 || natH <= 0) return;            // レイアウト未確定なら見送り
      var full = document.fullscreenElement === viewer;
      state.s = full
        ? clamp(Math.min(vw / natW, vh / natH))      // contain
        : clamp(Math.min(vw / natW, 1));             // 幅フィット(拡大せず)
      var sw = natW * state.s, sh = natH * state.s;
      state.x = sw < vw ? (vw - sw) / 2 : 0;              // 横: 収まれば中央/超えれば左
      state.y = sh < vh ? (vh - sh) / 2 : 0;              // 縦: 収まれば中央/超えれば上
      userAdjusted = false;                               // fit/reset で操作状態を解除
      schedule();
    }

    // ── toolbar ──
    var bar = document.createElement("div");
    bar.className = "diagram-toolbar";
    bar.appendChild(makeButton("−", "縮小 (Zoom out)", function () {
      var c = zoomFocus(); zoomTo(state.s / STEP, c.cx, c.cy);
    }));
    bar.appendChild(makeButton("+", "拡大 (Zoom in)", function () {
      var c = zoomFocus(); zoomTo(state.s * STEP, c.cx, c.cy);
    }));
    bar.appendChild(makeButton("⤢", "リセット/フィット (Reset)", fit));
    bar.appendChild(makeButton("⛶", "全画面 (Fullscreen)", function () {
      if (document.fullscreenElement === viewer) {
        if (document.exitFullscreen) document.exitFullscreen();
      } else if (viewer.requestFullscreen) {
        viewer.requestFullscreen();
      }
    }));
    viewer.appendChild(bar);

    // ── パン(ドラッグ)── マウスは touch-action に依らず動く。
    var dragging = false, moved = false;
    var sx = 0, sy = 0, ox = 0, oy = 0;
    stage.addEventListener("pointerdown", function (e) {
      if (e.button !== 0) return;
      measure();   // ドラッグ前に寸法/位置を最新化(直前のスクロール等を反映)
      dragging = true; moved = false;
      sx = e.clientX; sy = e.clientY; ox = state.x; oy = state.y;
      try { stage.setPointerCapture(e.pointerId); } catch (_) {}
      viewer.classList.add("is-grabbing");
    });
    stage.addEventListener("pointermove", function (e) {
      // パン中以外は、ズーム不動点用に直近ポインタ位置(viewer 座標)を更新する。
      // vw/vh はキャッシュ済み rect 由来。viewer の画面位置は別途 viewerLeft/Top で。
      if (!dragging) {
        lastPt = { cx: e.clientX - viewerLeft, cy: e.clientY - viewerTop };
        return;
      }
      var dx = e.clientX - sx, dy = e.clientY - sy;
      if (!moved && (Math.abs(dx) > DRAG || Math.abs(dy) > DRAG)) moved = true;
      if (moved) {
        state.x = ox + dx; state.y = oy + dy; userAdjusted = true;
        clampPan(); schedule();
      }
    });
    function endDrag(e) {
      if (!dragging) return;
      dragging = false;
      viewer.classList.remove("is-grabbing");
      try { stage.releasePointerCapture(e.pointerId); } catch (_) {}
    }
    stage.addEventListener("pointerup", endDrag);
    stage.addEventListener("pointercancel", endDrag);
    // 実ドラッグ直後の click(= 定義ジャンプ)は capture 段で握り潰す。
    stage.addEventListener("click", function (e) {
      if (moved) { e.preventDefault(); e.stopPropagation(); moved = false; }
    }, true);

    // viewer の画面位置だけを軽量に取り直す(自然寸は測らない)。ページスクロールで
    // left/top は変わるので、ポインタ系イベントの座標変換前に呼ぶ。
    function syncOrigin() {
      var vr = viewer.getBoundingClientRect();
      viewerLeft = vr.left; viewerTop = vr.top;
    }

    // ── ホイールズーム ──
    // 図上では素のホイールでズーム(巨大図を読むのに最重要の操作)。viewer 上だけ
    // preventDefault するので、図外のページスクロールは妨げない。修飾キー(Ctrl/⌘)
    // 併用時も同じくズーム。不動点はカーソル位置(見ている所へ寄る)。
    viewer.addEventListener("wheel", function (e) {
      e.preventDefault();
      syncOrigin();
      var factor = e.deltaY < 0 ? STEP : 1 / STEP;
      zoomTo(state.s * factor, e.clientX - viewerLeft, e.clientY - viewerTop);
    }, { passive: false });

    // ── ダブルクリックで局所拡大 ── 見たいノードを直接ダブルクリックすると、その
    // 点を不動点に 1 段大きく(×STEP²)寄る。巨大図で「読みたい所へ素早く寄る」最も
    // 直感的な操作。Alt/Shift 併用、または最大付近では逆に fit へ戻す(トグル感)。
    stage.addEventListener("dblclick", function (e) {
      e.preventDefault(); e.stopPropagation();
      syncOrigin();
      var cx = e.clientX - viewerLeft, cy = e.clientY - viewerTop;
      if (e.altKey || e.shiftKey || state.s >= MAX - 1e-6) { fit(); return; }
      zoomTo(state.s * STEP * STEP, cx, cy);
    });

    // 全画面遷移時の再フィット用に fit を保持(購読はモジュール単一リスナが担う)。
    viewer._refit = fit;

    // キーボード(viewer フォーカス時): +/= 拡大, - 縮小, 0 リセット, f 全画面。
    viewer.tabIndex = 0;
    viewer.addEventListener("keydown", function (e) {
      var c = zoomFocus();
      if (e.key === "+" || e.key === "=") zoomTo(state.s * STEP, c.cx, c.cy);
      else if (e.key === "-" || e.key === "_") zoomTo(state.s / STEP, c.cx, c.cy);
      else if (e.key === "0") fit();
      else if (e.key === "f" || e.key === "F") {
        if (document.fullscreenElement === viewer) {
          if (document.exitFullscreen) document.exitFullscreen();
        } else if (viewer.requestFullscreen) viewer.requestFullscreen();
      } else return;
      e.preventDefault();
    });

    // 初期フィット。mermaid SVG 挿入直後はレイアウトが未確定で自然寸が 0/不正に
    // なり、fit が early-return して一度も効かないことがある。2 段 RAF でレイアウト
    // 確定を 1 フレーム待ってから測って fit する(全画面遷移時と同じ確実さ)。
    requestAnimationFrame(function () { requestAnimationFrame(fit); });

    // viewer のサイズが変わる契機(ウィンドウリサイズ・サイドバー開閉・全画面の
    // 出入り・フォント/SVG の遅延ロードで自然寸が確定する瞬間)に自動で再フィット。
    // ユーザーがズーム/パンで動かした後の resize で勝手に戻さないよう、「まだ一度も
    // 操作していない or 現在 fit 相当」のときだけ再フィットする。初回測定の取りこぼ
    // し(自然寸 0 → 後から確定)も、この observer が拾って初期 fit を完成させる。
    if (typeof ResizeObserver !== "undefined") {
      var firstRO = true;
      var ro = new ResizeObserver(function () {
        // 自然寸が未確定だった初回や、ユーザー未操作のうちは fit を追従させる。
        if (firstRO) { firstRO = false; fit(); return; }
        if (!userAdjusted) fit();
        else { measure(); clampPan(); schedule(); } // 操作済みでも境界だけは保つ
      });
      ro.observe(viewer);
    }
  }

  // 全画面に入った/出た .diagram-viewer を「1 個の購読」で再フィットする。viewer
  // ごとに document リスナを足さないことでリスナのリークを避ける(_refit を目印)。
  // 全画面の出入りでは、その瞬間に getBoundingClientRect を測っても寸法がまだ
  // 全画面/通常へ更新されていないことがある。確実にレイアウト確定後へ回すため、
  // RAF を 2 段重ねる(1 フレーム待ってから測って fit)。全画面を出た viewer も
  // 通常サイズへ再フィットしたいので、fullscreenElement だけでなく直前に全画面
  // だった viewer も対象にする(_wasFullscreen を目印に引く)。
  function refitAfterLayout(el) {
    if (!el || !el._refit) return;
    requestAnimationFrame(function () { requestAnimationFrame(el._refit); });
  }
  var lastFs = null;
  document.addEventListener("fullscreenchange", function () {
    var fe = document.fullscreenElement;
    refitAfterLayout(fe);            // 入った先(あれば)
    if (lastFs && lastFs !== fe) refitAfterLayout(lastFs); // 出た元(あれば)
    lastFs = fe;
  });

  window.DiagramView = { attach: attach };
})();
