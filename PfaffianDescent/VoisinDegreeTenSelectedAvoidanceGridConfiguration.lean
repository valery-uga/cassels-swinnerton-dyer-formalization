import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridWitness
import PfaffianDescent.VoisinHypersurfaceFieldPointDescent

/-! # The selected grid vectors give an actual configuration of the original cubic -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

def voisinDegreeTenSelectedAvoidance_normalizedCubicPoint
    {L : Type u} [Field L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3)
    (v : Fin 4 → L) (hpv : p.eval v = 0) (hv0 : v 0 = 1) :
    Spec (.of L) ⟶ hypersurface p hp := by
  have hv : ∀ s ∈ (equationIdeal p hp).toIdeal, s.eval v = 0 := by
    intro s hs
    change s ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) L)) at hs
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hs
    rw [ht, map_mul, hpv, zero_mul]
  exact projectiveUnitVectorSchemePointAt (equationIdeal p hp) v hv 0 hv0

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_normalizedCubicPoint_toBase
    {L : Type u} [Field L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3)
    (v : Fin 4 → L) (hpv : p.eval v = 0) (hv0 : v 0 = 1) :
    voisinDegreeTenSelectedAvoidance_normalizedCubicPoint p hp v hpv hv0 ≫
      hypersurfaceToBase p hp = 𝟙 _ := by
  unfold voisinDegreeTenSelectedAvoidance_normalizedCubicPoint
  dsimp only
  change projectiveUnitVectorSchemePointAt (equationIdeal p hp) v _ 0 hv0 ≫
    toBase (equationIdeal p hp) = _
  rw [projectiveUnitVectorSchemePointAt_toBase]
  exact Spec.map_id _

theorem voisinDegreeTenSelectedAvoidance_normalizedCubicPoint_injective
    {L : Type u} [Field L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3)
    (v w : Fin 4 → L) (hpv : p.eval v = 0) (hpw : p.eval w = 0)
    (hv0 : v 0 = 1) (hw0 : w 0 = 1)
    (h : voisinDegreeTenSelectedAvoidance_normalizedCubicPoint p hp v hpv hv0 =
      voisinDegreeTenSelectedAvoidance_normalizedCubicPoint p hp w hpw hw0) : v = w := by
  unfold voisinDegreeTenSelectedAvoidance_normalizedCubicPoint at h
  exact projectiveUnitVectorSchemePointAt_injective (equationIdeal p hp) 0 _ _ hv0 hw0 h

set_option backward.isDefEq.respectTransparency false in
/-- The actual normalized points remain distinct after restriction to the
original coefficient field and give an actual ordered configuration there.
Its coordinate maps are the literal coefficient-restricted native points. -/
theorem voisinDegreeTenSelectedAvoidance_exists_ordered_configuration_of_normalized_vectors
    {K L : Type u} [Field K] [Field L] (b : K →+* L)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {n : ℕ} (v : Fin n → Fin 4 → L)
    (hvinj : Function.Injective v)
    (hpv : ∀ i, (p.map b).eval (v i) = 0) (hv0 : ∀ i, v i 0 = 1) :
    ∃ A : Spec (.of L) ⟶
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left,
      A ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).hom =
        Spec.map (CommRingCat.ofHom b) ∧
      ∀ i, (A ≫ Over.Hom.left
          (orderedFamilyConfigurationι (hypersurfaceToBase p hp) n)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) n i).left =
        voisinDegreeTenSelectedAvoidance_normalizedCubicPoint
          (p.map b) (hp.map b) (v i) (hpv i) (hv0 i) ≫
          projectiveCoefficientMap b (equationIdeal p hp)
            (equationIdeal (p.map b) (hp.map b)) (equationIdeal_map b p hp) := by
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    isSeparated_homogeneousToBase (equationIdeal p hp)
  let x : Fin n → (Spec (.of L) ⟶ hypersurface (p.map b) (hp.map b)) :=
    fun i => voisinDegreeTenSelectedAvoidance_normalizedCubicPoint
      (p.map b) (hp.map b) (v i) (hpv i) (hv0 i)
  have hxbase : ∀ i, x i ≫ hypersurfaceToBase (p.map b) (hp.map b) = 𝟙 _ :=
    fun i => voisinDegreeTenSelectedAvoidance_normalizedCubicPoint_toBase
      (p.map b) (hp.map b) (v i) (hpv i) (hv0 i)
  let f : hypersurface (p.map b) (hp.map b) ⟶ hypersurface p hp :=
    projectiveCoefficientMap b (equationIdeal p hp)
      (equationIdeal (p.map b) (hp.map b)) (equationIdeal_map b p hp)
  have hfbase : f ≫ hypersurfaceToBase p hp =
      hypersurfaceToBase (p.map b) (hp.map b) ≫ Spec.map (CommRingCat.ofHom b) :=
    projectiveCoefficientMap_toBase b (equationIdeal p hp)
      (equationIdeal (p.map b) (hp.map b)) (equationIdeal_map b p hp)
  let q : Fin n → (Spec (.of L) ⟶ hypersurface p hp) := fun i => x i ≫ f
  have hqbase : ∀ i, q i ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom b) := by
    intro i
    dsimp only [q]
    rw [Category.assoc, hfbase, ← Category.assoc, hxbase i, Category.id_comp]
  have hqdist : ∀ i j, i ≠ j → q i ≠ q j := by
    intro i j hij heq
    apply hij
    apply hvinj
    apply voisinDegreeTenSelectedAvoidance_normalizedCubicPoint_injective
      (p.map b) (hp.map b) (v i) (v j) (hpv i) (hpv j) (hv0 i) (hv0 j)
    exact hypersurfaceCoefficientChange_injective_on_fieldPoints b p hp
      (x i) (x j) (hxbase i) (hxbase j) heq
  exact exists_orderedConfigurationFieldPoint (hypersurfaceToBase p hp) n
    (Spec.map (CommRingCat.ofHom b)) q hqbase hqdist

set_option backward.isDefEq.respectTransparency false in
/-- The concrete grid gives a genuine field-valued point of the original
ordered sixteen-point configuration, with surjective literal cubic
restriction and the two explicit proper-intersection equations in its kernel.
Every coordinate is retained in the fixed chart `X₀ = 1`. -/
theorem voisinDegreeTenSelectedAvoidance_exists_sixteen_grid_configuration
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    ∃ (v : Fin 16 → Fin 4 → L) (hv0 : ∀ i, v i 0 = 1)
      (hpv : ∀ i, (p.map (algebraMap K L)).eval (v i) = 0)
      (A : Spec (.of L) ⟶
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left),
      Function.Injective v ∧
      A ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).hom =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) ∧
      (∀ i, (A ≫ Over.Hom.left
          (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 16)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 16 i).left =
        voisinDegreeTenSelectedAvoidance_normalizedCubicPoint
          (p.map (algebraMap K L)) (hp.map (algebraMap K L))
          (v i) (hpv i) (hv0 i) ≫
          projectiveCoefficientMap (algebraMap K L) (equationIdeal p hp)
            (equationIdeal (p.map (algebraMap K L)) (hp.map (algebraMap K L)))
            (equationIdeal_map (algebraMap K L) p hp)) ∧
      Function.Surjective (eval₂Hom (algebraMap L (Fin 16 → L)) (fun j i => v i j)) ∧
      Function.Surjective (homogeneousSectionRestriction (K := L) (fun j i => v i j) 3) ∧
      (voisinDegreeTenSelectedAvoidance_gridCubic L 1).eval₂
        (algebraMap L (Fin 16 → L)) (fun j i => v i j) = 0 ∧
      (voisinDegreeTenSelectedAvoidance_gridCubic L 2).eval₂
        (algebraMap L (Fin 16 → L)) (fun j i => v i j) = 0 := by
  obtain ⟨v, hvinj, hv0, heval, hcubic, hpzero, hqzero, hrzero⟩ :=
    voisinDegreeTenSelectedAvoidance_exists_sixteen_grid_witness (L := L) p hp hno
  have hpv : ∀ i, (p.map (algebraMap K L)).eval (v i) = 0 := by
    intro i
    have hi := congrFun hpzero i
    rw [finite_product_evaluation_apply] at hi
    simpa using hi
  obtain ⟨A, hAbase, hAcoord⟩ :=
    voisinDegreeTenSelectedAvoidance_exists_ordered_configuration_of_normalized_vectors
      (algebraMap K L) p hp v hvinj hpv hv0
  exact ⟨v, hv0, hpv, A, hvinj, hAbase, hAcoord, heval, hcubic, hqzero, hrzero⟩

end PfaffianDescent
