VIEWER := "okular"
ENTRY := "thesis.typ"
ARTIFACT := "thesis.pdf"
SYNC_PATH := "~/uni/ba/thesis.pdf"

alias c := compile
alias w := watch
alias e := edit
alias o := open
alias wo := watch-open
alias fmt := format
alias s := sync

compile:
	typst compile {{ENTRY}}

watch:
	typst watch {{ENTRY}}

edit:
	$EDITOR {{ENTRY}}

open:
	{{VIEWER}} {{ARTIFACT}} &

watch-open: open watch

format:
	typstyle --inplace .

check-format:
	typstyle --check .

clean:
	fd --no-ignore -e pdf -x rm -v {}

configure-git-hooks:
	git config core.hooksPath scripts/git-hooks

sync: compile
	cp {{ARTIFACT}} {{SYNC_PATH}}
