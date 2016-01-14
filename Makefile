all: FJ_Example.vo

AdditionalTactics.vo AdditionalTactics.glob AdditionalTactics.v.beautified: AdditionalTactics.v
Atom.vo Atom.glob Atom.v.beautified: Atom.v
FJ_Definitions.vo FJ_Definitions.glob FJ_Definitions.v.beautified: FJ_Definitions.v Metatheory.vo
FJ_Example.vo FJ_Example.glob FJ_Example.v.beautified: FJ_Example.v AdditionalTactics.vo Metatheory.vo FJ_Definitions.vo FJ_Facts.vo FJ_Properties.vo
FJ_Facts.vo FJ_Facts.glob FJ_Facts.v.beautified: FJ_Facts.v AdditionalTactics.vo Metatheory.vo FJ_Definitions.vo
FJ_Properties.vo FJ_Properties.glob FJ_Properties.v.beautified: FJ_Properties.v AdditionalTactics.vo Metatheory.vo FJ_Definitions.vo FJ_Facts.vo
Metatheory.vo Metatheory.glob Metatheory.v.beautified: Metatheory.v AdditionalTactics.vo Atom.vo

%.vo : %.v
	coqc $<
