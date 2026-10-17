import PfaffianDescent.NilpotentCartesianFieldPointSupport176

/-! SOURCE ONLY312. A whole nilpotent Cartesian reduction forces the SAME
entire lifted source into any fixed open containing the whole old family.
This is not a supplied lift or a good-base restriction. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

lemma nilpotentReduction_fixedOpen_containsWholeLift312
    {R S : Type u} [CommRing R] [CommRing S] {X X0 Z Z0 : Scheme.{u}}
    (b : R →+* S) (hb : Function.Surjective b) (hnil : IsNilpotent (RingHom.ker b))
    (F : X ⟶ Spec (.of R)) (F0 : X0 ⟶ Spec (.of S))
    (d : X0 ⟶ X) (i : Z ⟶ X) (i0 : Z0 ⟶ X0) (r : Z0 ⟶ Z)
    (Hbase : IsPullback r (i0 ≫ F0) (i ≫ F) (Spec.map (CommRingCat.ofHom b)))
    (hcomm : r ≫ i = i0 ≫ d) (U : X.Opens)
    (hU : ∀ z : Z0, (i0 ≫ d) z ∈ U) : ∀ z : Z, i z ∈ U := by
  letI : Surjective r := surjective_cartesianFamilyFiber_of_nilpotent_kernel176
    (i ≫ F) b hb hnil r (i0 ≫ F0) Hbase
  intro z
  obtain ⟨z0, rfl⟩ := r.surjective z
  have he : i (r z0) = (i0 ≫ d) z0 := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun f => f z0) hcomm
  exact he.symm ▸ hU z0

/-- Native factor keeps the whole original source and is genuinely closed. -/
lemma exists_fixedOpen_factor_of_nilpotentReduction312
    {R S : Type u} [CommRing R] [CommRing S] {X X0 Z Z0 : Scheme.{u}}
    (b : R →+* S) (hb : Function.Surjective b) (hnil : IsNilpotent (RingHom.ker b))
    (F : X ⟶ Spec (.of R)) (F0 : X0 ⟶ Spec (.of S))
    (d : X0 ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] (i0 : Z0 ⟶ X0)
    (r : Z0 ⟶ Z)
    (Hbase : IsPullback r (i0 ≫ F0) (i ≫ F) (Spec.map (CommRingCat.ofHom b)))
    (hcomm : r ≫ i = i0 ≫ d) (U : X.Opens)
    (hU : ∀ z : Z0, (i0 ≫ d) z ∈ U) :
    ∃ a : Z ⟶ U, a ≫ U.ι = i ∧ IsClosedImmersion a := by
  have hall := nilpotentReduction_fixedOpen_containsWholeLift312
    b hb hnil F F0 d i i0 r Hbase hcomm U hU
  have hrange : Set.range i ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact hall z
  let a := IsOpenImmersion.lift U.ι i hrange
  have ha : a ≫ U.ι = i := IsOpenImmersion.lift_fac U.ι i hrange
  letI : IsClosedImmersion (a ≫ U.ι) := ha.symm ▸ inferInstanceAs (IsClosedImmersion i)
  exact ⟨a, ha, IsClosedImmersion.of_comp a U.ι⟩

end PfaffianDescent
end
