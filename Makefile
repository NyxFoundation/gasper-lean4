.PHONY: install clean_noise_text_from_specific_file up audit md_export md_export_ex verso-facet comments_clean

install:
	lake update
	lake exe cache get

# Lean / audit log
clean_noise_text_from_specific_file:
	@test -n "$(FILE)" || (echo "clean_noise_text_from_specific_file: set FILE=path/to/file" >&2; exit 1)
	@test -f "$(FILE)" || (echo "clean_noise_text_from_specific_file: not a file: $(FILE)" >&2; exit 1)
	@set -e; \
	tmp="$$(mktemp)"; \
	trap 'rm -f "$$tmp"' EXIT; \
	sed -E \
		-e '/^[[:space:]]*use `set_option diagnostics\.threshold <num>` to control threshold for reporting counters[[:space:]]*$$/d' \
		-e '/^[[:space:]]*Note: This linter can be disabled with `set_option linter\.unusedSectionVars false`[[:space:]]*$$/d' \
		-e '/^[[:space:]]*Note: This linter can be disabled with `set_option linter\.unusedVariables false`[[:space:]]*$$/d' \
		-e '/^[[:space:]]*GasperBeaconChain\/Audit\/Automated\/DefaultBuildAudit\.lean:5:0:[[:space:]]*$$/d' \
		-e 's|GasperBeaconChain/Audit/Automated/DefaultBuildAudit\.lean:5:0:[[:space:]]*||g' \
		"$(FILE)" > "$$tmp"; \
	mv "$$tmp" "$(FILE)"; \
	trap - EXIT

LEAN_AUDIT_PATH=./log/
up:
	@set +e; \
	{ lake build; } > "$(LEAN_AUDIT_PATH)build.log" 2>&1; \
	status="$$?"; \
	set -e; \
	$(MAKE) clean_noise_text_from_specific_file FILE="$(LEAN_AUDIT_PATH)build.log"; \
	$(MAKE) md_export; \
	$(MAKE) md_export_ex; \
	tail -n 150 "$(LEAN_AUDIT_PATH)build.log"; \
	echo "'if you need full output log result, use file: $(LEAN_AUDIT_PATH)build.log'"; \
	exit "$$status"

audit:
	@set +e; \
	{ lake build GasperBeaconChain.Audit.Automated.DefaultBuildAudit; } > "$(LEAN_AUDIT_PATH)audit.log" 2>&1; \
	status="$$?"; \
	set -e; \
	$(MAKE) clean_noise_text_from_specific_file FILE="$(LEAN_AUDIT_PATH)audit.log"; \
	$(MAKE) md_export; \
	$(MAKE) md_export_ex; \
	tail -n 150 "$(LEAN_AUDIT_PATH)audit.log"; \
	echo "'if you need full output log result, use file: $(LEAN_AUDIT_PATH)audit.log'"; \
	exit "$$status"

PROJECT_DIR=GasperBeaconChain/Core
OUTPUT_MD=ImpTree-Lean.md

md_export:
	@set -e; \
	tmp="$$(mktemp)"; \
	trap 'rm -f "$$tmp"' EXIT; \
	echo "Generating $(OUTPUT_MD) from $(PROJECT_DIR)..."; \
	{ \
		echo "# Lean Sources - 実装 全体俯瞰用"; \
		echo; \
		echo "**※現在の実装は、以下の様に成って居ます。**"; \
		echo; \
		echo "---"; \
		echo; \
		echo "Project: \`$(PROJECT_DIR)\`"; \
		echo; \
		echo "## Directory Tree"; \
		echo; \
		echo '```text'; \
		tree "$(PROJECT_DIR)"; \
		echo '```'; \
		echo; \
		echo "## Files"; \
		echo; \
		find "$(PROJECT_DIR)" -type f -name '*.lean' | sort | while read -r file; do \
			rel="$${file#$(PROJECT_DIR)/}"; \
			echo "### $$rel"; \
			echo; \
			echo '```lean'; \
			cat "$$file"; \
			echo; \
			echo '```'; \
			echo; \
		done; \
	} > "$$tmp"; \
	mv "$$tmp" "$(OUTPUT_MD)"; \
	trap - EXIT; \
	echo "Done: ./$(OUTPUT_MD)"

PROJECT_EXC_DIR=GasperBeaconChain/Executable
OUTPUT_EXC_MD=ImpTree-Executable-Lean.md

md_export_ex:
	@set -e; \
	tmp="$$(mktemp)"; \
	trap 'rm -f "$$tmp"' EXIT; \
	echo "Generating $(OUTPUT_EXC_MD) from $(PROJECT_EXC_DIR)..."; \
	{ \
		echo "# Lean Sources - 実装 全体俯瞰用"; \
		echo; \
		echo "**※現在の実装は、以下の様に成って居ます。**"; \
		echo; \
		echo "---"; \
		echo; \
		echo "Project: \`$(PROJECT_EXC_DIR)\`"; \
		echo; \
		echo "## Directory Tree"; \
		echo; \
		echo '```text'; \
		tree "$(PROJECT_EXC_DIR)"; \
		echo '```'; \
		echo; \
		echo "## Files"; \
		echo; \
		find "$(PROJECT_EXC_DIR)" -type f -name '*.lean' | sort | while read -r file; do \
			rel="$${file#$(PROJECT_EXC_DIR)/}"; \
			echo "### $$rel"; \
			echo; \
			echo '```lean'; \
			cat "$$file"; \
			echo; \
			echo '```'; \
			echo; \
		done; \
	} > "$$tmp"; \
	mv "$$tmp" "$(OUTPUT_EXC_MD)"; \
	trap - EXIT; \
	echo "Done: ./$(OUTPUT_EXC_MD)"

# ========== 経路 B: パッケージファセット(literate.toml あり・一発) ==========
# 3 段パイプライン:
#   1. lake build          … .olean キャッシュ(Lean ソースのみ。~30s cached)
#   2. lake build :literate … #mermaid_explode 等の elaboration + JSON 生成
#                             (MermaidRef 変更後は ~800s、キャッシュ時 ~0s)
#   3. lake build :literateHtml … JSON → HTML(~4s。:literate が stale だと
#                             ここで :literate を再ビルドするため遅く見える)
# :literate を明示的に挟むことで、:literateHtml は常に高速(~4s)になる。
verso-facet:
	lake build
	lake build :literate
	lake build :literateHtml
	cp -r static/katex/fonts .lake/build/literate-html/
	@echo "=========== done ==========="
	python3 -m http.server 8000 -d .lake/build/literate-html

# ========== GitHub Pages 用ビルド(verso-facet のサーバー無し版) ==========
# `make verso-pages` → docs/ に静的サイトを生成。
# GitHub リポジトリの Settings > Pages > Source を "Deploy from a branch",
# Branch を "main" (or develop), folder を "/docs" に設定する。
# .nojekyll: Jekyll を無効化(-verso-docs.json, -verso-search/ がハイフン始まり
#   のため、Jekyll が処理対象外にするのを防ぐ)。
verso-pages:
	lake build
	lake build :literate
	lake build :literateHtml
	cp -r static/katex/fonts .lake/build/literate-html/
	rm -rf docs
	cp -r .lake/build/literate-html docs
	touch docs/.nojekyll
	@echo "=========== docs/ ready for GitHub Pages ==========="

# usage: python3 scripts/remove_lean_comments.py <Lean-directory-or-file>
# USAGE: make comments_clean F=./Test/
comments_clean:
	python3 ./Workbench/scripts/remove_lean_comments.py $(F)  > "$(LEAN_AUDIT_PATH)remove_lean_comments.log" 

