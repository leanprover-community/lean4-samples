theorem not_iff_imp_false (P : Prop) : ¬Nonempty P ↔ P → False :=
  ⟨fun h a => h ⟨a⟩, fun h ⟨a⟩ => h a⟩