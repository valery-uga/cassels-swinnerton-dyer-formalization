import PfaffianDescent.PointCartierYonedaPointQuotient

/-! # The ambient and surface point quotients are canonically isomorphic -/

noncomputable section

namespace PfaffianDescent

variable {R : Type*} [CommRing R]

theorem pointCartierYonedaPointQuotient_preimage_mem
    (f g h p : R) (v : Rˣ) (b c : R)
    (heq : p = f * (v : R) + g * b + h * c) (x : R)
    (hx : Ideal.Quotient.mk (Ideal.span {p}) x ∈ Ideal.span
      ({Ideal.Quotient.mk (Ideal.span {p}) g,
        Ideal.Quotient.mk (Ideal.span {p}) h} : Set (R ⧸ Ideal.span {p}))) :
    x ∈ Ideal.span ({f, g, h} : Set R) := by
  rw [← twoGeneratorLast_range] at hx
  obtain ⟨⟨a, d⟩, had⟩ := hx
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨d', rfl⟩ := Ideal.Quotient.mk_surjective d
  have hzero : Ideal.Quotient.mk (Ideal.span {p}) (x - (g * a' + h * d')) = 0 := by
    change Ideal.Quotient.mk (Ideal.span {p}) g * Ideal.Quotient.mk (Ideal.span {p}) a' +
      Ideal.Quotient.mk (Ideal.span {p}) h * Ideal.Quotient.mk (Ideal.span {p}) d' =
        Ideal.Quotient.mk (Ideal.span {p}) x at had
    rw [map_sub, map_add, map_mul, map_mul, had, sub_self]
  have hrem := Ideal.Quotient.eq_zero_iff_mem.mp hzero
  have hpI : p ∈ Ideal.span ({f, g, h} : Set R) := by
    rw [heq]
    apply Ideal.add_mem
    · apply Ideal.add_mem
      · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
      · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  have hspan : Ideal.span {p} ≤ Ideal.span ({f, g, h} : Set R) :=
    Ideal.span_le.mpr (by
      intro y hy
      have hyp : y = p := Set.mem_singleton_iff.mp hy
      subst y
      exact hpI)
  have hrest : g * a' + h * d' ∈ Ideal.span ({f, g, h} : Set R) :=
    Ideal.add_mem _
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
  simpa only [sub_add_cancel] using Ideal.add_mem _ (hspan hrem) hrest

theorem pointCartierYonedaPointQuotientMap_bijective
    (f g h p : R) (v : Rˣ) (b c : R)
    (heq : p = f * (v : R) + g * b + h * c) :
    Function.Bijective (pointCartierYonedaPointQuotientMap f g h p v b c heq) := by
  constructor
  · have hzero : ∀ z, pointCartierYonedaPointQuotientMap f g h p v b c heq z = 0 → z = 0 := by
      intro z hz
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      rw [pointCartierYonedaPointQuotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at hz
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (pointCartierYonedaPointQuotient_preimage_mem f g h p v b c heq x hz)
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hxy, sub_self]
  · intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk (Ideal.span ({f, g, h} : Set R)) x, rfl⟩

/-- The quotient isomorphism is induced by the two actual augmentations. -/
def pointCartierYonedaPointQuotientEquiv
    (f g h p : R) (v : Rˣ) (b c : R)
    (heq : p = f * (v : R) + g * b + h * c) :
    (R ⧸ Ideal.span ({f, g, h} : Set R)) ≃ₗ[R]
      ((R ⧸ Ideal.span {p}) ⧸ Ideal.span
        ({Ideal.Quotient.mk (Ideal.span {p}) g,
          Ideal.Quotient.mk (Ideal.span {p}) h} : Set (R ⧸ Ideal.span {p}))) :=
  LinearEquiv.ofBijective (pointCartierYonedaPointQuotientMap f g h p v b c heq)
    (pointCartierYonedaPointQuotientMap_bijective f g h p v b c heq)

end PfaffianDescent
