module

/-! `meta` code whose compiled form uses an auxiliary `_boxed_const` constant. -/

public meta def prob : Float := 0.75
/-- Boxing the non-ground constant `prob` creates an auxiliary `_boxed_const` declaration. -/
public meta def probs : Array Float := #[prob, prob, 0.5]
public meta def sumProbs : Float := probs.foldl (· + ·) 0
