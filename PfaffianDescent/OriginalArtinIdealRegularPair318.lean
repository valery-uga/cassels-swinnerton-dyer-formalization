import PfaffianDescent.ArtinBaseRegularPair318
import PfaffianDescent.HilbertBurchRegularPairPowers318

/-!
An actual regular pair in the entire special-fiber
ideal is lifted inside the original ideal. Original reduction maps and
generator values are retained, and regularity is derived by devissage.
-/

noncomputable section
namespace AllCharacteristics
open Module TensorProduct
universe u v w

lemma regularPair_map_ringEquiv318
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (e : A ≃+* B) (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b) :
    IsSMulRegular B (e a) ∧ IsSMulRegular (B ⧸ Ideal.span {e a}) (e b) := by
  have ha' : IsSMulRegular B (e a) := by
    intro x y hxy
    change e a * x = e a * y at hxy
    apply e.symm.injective
    apply ha
    change a * e.symm x = a * e.symm y
    simpa only [map_mul, RingEquiv.symm_apply_apply] using congrArg e.symm hxy
  have hmap : Ideal.span ({e a} : Set B) =
      (Ideal.span ({a} : Set A)).map (e : A →+* B) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  let eQ := Ideal.quotientEquiv (Ideal.span {a}) (Ideal.span {e a}) e hmap
  have hcompat : ∀ x : A ⧸ Ideal.span {a}, eQ (b • x) = e b • eQ x := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change eQ (Ideal.Quotient.mk (Ideal.span {a}) (b * x)) =
      Ideal.Quotient.mk (Ideal.span {e a}) (e b * e x)
    exact (Ideal.quotientEquiv_mk (Ideal.span {a}) (Ideal.span {e a}) e hmap
      (b * x)).trans (congrArg (Ideal.Quotient.mk (Ideal.span {e a})) (e.map_mul b x))
  exact ⟨ha', (eQ.toEquiv.isSMulRegular_congr hcompat).mp hb⟩

theorem exists_originalIdeal_regularPair_lifts318
    {R : Type u} {A : Type v} {A₀ : Type w}
    [CommRing R] [CommRing A] [CommRing A₀] [Algebra R A] [Module.Flat R A]
    (I : Ideal R) [I.IsMaximal] (hI : IsNilpotent I)
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : RingHom.ker π = I.map (algebraMap R A))
    (J : Ideal A) (a₀ b₀ : A₀)
    (haJ : a₀ ∈ J.map π) (hbJ : b₀ ∈ J.map π)
    (ha₀ : IsSMulRegular A₀ a₀)
    (hb₀ : IsSMulRegular (A₀ ⧸ Ideal.span {a₀}) b₀) :
    ∃ a b : A, a ∈ J ∧ b ∈ J ∧ π a = a₀ ∧ π b = b₀ ∧
      IsSMulRegular A a ∧ IsSMulRegular (A ⧸ Ideal.span {a}) b := by
  obtain ⟨a, ha, haπ⟩ := (Ideal.mem_map_iff_of_surjective π hπ).mp haJ
  obtain ⟨b, hb, hbπ⟩ := (Ideal.mem_map_iff_of_surjective π hπ).mp hbJ
  let k := R ⧸ I
  let B := k ⊗[R] A
  let K := I.map (algebraMap R A)
  let e₀ : (A ⧸ K) ≃+* A₀ :=
    (Ideal.quotEquivOfEq hker.symm).trans (π.quotientKerEquivOfSurjective hπ)
  let eB : (A ⧸ K) ≃+* B :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I).toRingEquiv
  let e : A₀ ≃+* B := e₀.symm.trans eB
  have he₀ (x : A) : e₀ (Ideal.Quotient.mk K x) = π x := by
    change π.quotientKerEquivOfSurjective hπ
      ((Ideal.quotEquivOfEq hker.symm) (Ideal.Quotient.mk K x)) = π x
    rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  have he (x : A) : e (π x) = (1 : k) ⊗ₜ[R] x := by
    change eB (e₀.symm (π x)) = _
    rw [← he₀ x, e₀.symm_apply_apply]
    exact Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk A I x
  obtain ⟨haB, hbB⟩ := regularPair_map_ringEquiv318 e a₀ b₀ ha₀ hb₀
  have heA : e a₀ = (1 : k) ⊗ₜ[R] a := by rw [← haπ, he]
  have heB : e b₀ = (1 : k) ⊗ₜ[R] b := by rw [← hbπ, he]
  have haTensor : IsSMulRegular B ((1 : k) ⊗ₜ[R] a) := by
    rw [heA] at haB
    exact haB
  have hbTensor : IsSMulRegular (B ⧸ Ideal.span {((1 : k) ⊗ₜ[R] a)})
      ((1 : k) ⊗ₜ[R] b) := by
    rw [heA, heB] at hbB
    exact hbB
  obtain ⟨haActual, hbActual, hflatA, hflatAB⟩ :=
    regularPair_of_nilpotent_residue318 I hI a b haTensor hbTensor
  exact ⟨a, b, ha, hb, haπ, hbπ, haActual, hbActual⟩

/-- The relative ideal contains an ACTUAL regular pair, constructed from
its finite-length special fiber on a regular local surface. The original
relative ideal need not be a complete intersection or have two generators.
Neither flatness of the pair quotient nor ambient regularity is assumed. -/
theorem exists_regularPair_in_originalIdeal_of_regularSurface_fiber318
    {R : Type u} {A : Type v} {A₀ : Type w}
    [CommRing R] [CommRing A] [CommRing A₀] [Algebra R A] [Module.Flat R A]
    [IsRegularLocalRing A₀] (hdim : ringKrullDim A₀ = 2)
    (I : Ideal R) [I.IsMaximal] (hI : IsNilpotent I)
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : RingHom.ker π = I.map (algebraMap R A))
    (J : Ideal A) [IsArtinianRing (A₀ ⧸ J.map π)] :
    ∃ a b : A, a ∈ J ∧ b ∈ J ∧ IsSMulRegular A a ∧
      IsSMulRegular (A ⧸ Ideal.span {a}) b := by
  obtain ⟨a₀, b₀, haJ, hbJ, ha₀, hb₀⟩ :=
    AllCharacteristics.HilbertSurfaceDraft.exists_regular_pair_in_ideal_of_artinian_quotient
      hdim (J.map π)
  obtain ⟨a, b, ha, hb, haπ, hbπ, haActual, hbActual⟩ :=
    exists_originalIdeal_regularPair_lifts318 I hI π hπ hker J a₀ b₀ haJ hbJ ha₀ hb₀
  exact ⟨a, b, ha, hb, haActual, hbActual⟩

end AllCharacteristics
end
