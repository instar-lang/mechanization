.DEFAULT_GOAL := all

basic:
	lake build Instar.TwoLevelBasic.Defs

rec:
	lake build Instar.TwoLevelRec.Defs

mut:
	lake build Instar.TwoLevelMut.Defs

final:
	lake build Instar.TwoLevelFinal.Defs

brack:
	lake build Instar.TwoLevelRecBrack.Defs

all: basic rec mut final brack
