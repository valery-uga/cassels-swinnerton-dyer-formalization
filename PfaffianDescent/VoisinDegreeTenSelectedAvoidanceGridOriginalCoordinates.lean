import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridWitness
import PfaffianDescent.VoisinSelectedVectorCoordinateSpecialization
import AllCharacteristics.OrderedConfigurationFieldPoints

/-! # The grid configuration directly in the original cubic's normalized chart -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial Module HomogeneousLocalization
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

theorem voisinDegreeTenSelectedAvoidance_equationIdeal_eval₂_zero
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (v : Fin 4 → L) (hpv : p.eval₂ (algebraMap K L) v = 0) :
    ∀ s ∈ (equationIdeal p hp).toIdeal, s.eval₂ (algebraMap K L) v = 0 := by
  intro s hs
  change s ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) at hs
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hs
  rw [ht, eval₂_mul, hpv, zero_mul]

def voisinDegreeTenSelectedAvoidance_normalizedCubicPointOver
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (v : Fin 4 → L) (hpv : p.eval₂ (algebraMap K L) v = 0) (hv0 : v 0 = 1) :
    Spec (.of L) ⟶ hypersurface p hp :=
  linearNormalizedPointAt (equationIdeal p hp) v
    (voisinDegreeTenSelectedAvoidance_equationIdeal_eval₂_zero p hp v hpv)
    (coordinate (equationIdeal p hp) 0) (coordinate_mem (equationIdeal p hp) 0)
    (by change (eval₂Hom (algebraMap K L) v) (X 0) = 1; simpa using hv0)

theorem voisinDegreeTenSelectedAvoidance_normalizedCubicPointOver_toBase
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (v : Fin 4 → L) (hpv : p.eval₂ (algebraMap K L) v = 0) (hv0 : v 0 = 1) :
    voisinDegreeTenSelectedAvoidance_normalizedCubicPointOver p hp v hpv hv0 ≫
      hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  exact linearNormalizedPointAt_toBase (equationIdeal p hp) v _ _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_normalizedCubicPointOver_injective
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (v w : Fin 4 → L) (hpv : p.eval₂ (algebraMap K L) v = 0)
    (hpw : p.eval₂ (algebraMap K L) w = 0) (hv0 : v 0 = 1) (hw0 : w 0 = 1)
    (h : voisinDegreeTenSelectedAvoidance_normalizedCubicPointOver p hp v hpv hv0 =
      voisinDegreeTenSelectedAvoidance_normalizedCubicPointOver p hp w hpw hw0) : v = w := by
  let I := equationIdeal p hp
  let heV := voisinDegreeTenSelectedAvoidance_equationIdeal_eval₂_zero p hp v hpv
  let heW := voisinDegreeTenSelectedAvoidance_equationIdeal_eval₂_zero p hp w hpw
  have hOneV : (Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K L) v) heV)
      (coordinate I 0) = 1 := by
    change (eval₂Hom (algebraMap K L) v) (X 0) = 1
    simpa using hv0
  have hOneW : (Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K L) w) heW)
      (coordinate I 0) = 1 := by
    change (eval₂Hom (algebraMap K L) w) (X 0) = 1
    simpa using hw0
  simp only [voisinDegreeTenSelectedAvoidance_normalizedCubicPointOver,
    linearNormalizedPointAt] at h
  have hmaps := (cancel_mono (Proj.awayι (grading I) (coordinate I 0)
    (coordinate_mem I 0) (by decide : 0 < 1))).mp h
  have hring := Spec.map_injective hmaps
  funext j
  have hj := congrArg (fun g : CommRingCat.of (Away (grading I) (coordinate I 0)) ⟶
      CommRingCat.of L => g (linearChartCoordinate I (coordinate I 0) (coordinate_mem I 0) j)) hring
  change linearNormalizedPointChartMapAt I v heV (coordinate I 0)
      (coordinate_mem I 0) hOneV (linearChartCoordinate I (coordinate I 0) (coordinate_mem I 0) j) =
    linearNormalizedPointChartMapAt I w heW (coordinate I 0)
      (coordinate_mem I 0) hOneW (linearChartCoordinate I (coordinate I 0) (coordinate_mem I 0) j) at hj
  rw [linearNormalizedPointChartMapAt_coordinate, linearNormalizedPointChartMapAt_coordinate] at hj
  exact hj

set_option backward.isDefEq.respectTransparency false in
/-- Actual chart-coordinate sections specialize to the unaltered selected
vector coordinates for the directly constructed original-field point. -/
theorem voisinDegreeTenSelectedAvoidance_normalizedCubicPointOver_pulled_coordinate
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (v : Fin 4 → L) (hpv : p.eval₂ (algebraMap K L) v = 0) (hv0 : v 0 = 1)
    (U : Scheme.{u}) (a : Spec (.of L) ⟶ U)
    (t : U ⟶ Spec (.of (Away (grading (equationIdeal p hp)) (coordinate (equationIdeal p hp) 0))))
    (hpoint : (a ≫ t) ≫ Proj.awayι (grading (equationIdeal p hp))
      (coordinate (equationIdeal p hp) 0) (coordinate_mem (equationIdeal p hp) 0)
      (by decide : 0 < 1) =
      voisinDegreeTenSelectedAvoidance_normalizedCubicPointOver p hp v hpv hv0)
    (j : Fin 4) :
    a.appTop.hom (pulledLinearChartCoordinate (equationIdeal p hp)
      (coordinate (equationIdeal p hp) 0) (coordinate_mem (equationIdeal p hp) 0) U t j) =
      (StructureSheaf.globalSectionsIso L).hom (v j) := by
  exact pulledLinearChartCoordinate_value_of_normalizedPointAt (equationIdeal p hp)
    (coordinate (equationIdeal p hp) 0) (coordinate_mem (equationIdeal p hp) 0) v
    (voisinDegreeTenSelectedAvoidance_equationIdeal_eval₂_zero p hp v hpv) _ U a t hpoint j

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_exists_ordered_configuration_over_original
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {n : ℕ} (v : Fin n → Fin 4 → L) (hvinj : Function.Injective v)
    (hpv : ∀ i, p.eval₂ (algebraMap K L) (v i) = 0) (hv0 : ∀ i, v i 0 = 1) :
    ∃ A : Spec (.of L) ⟶
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left,
      A ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).hom =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) ∧
      ∀ i, (A ≫ Over.Hom.left
          (orderedFamilyConfigurationι (hypersurfaceToBase p hp) n)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) n i).left =
        voisinDegreeTenSelectedAvoidance_normalizedCubicPointOver p hp (v i) (hpv i) (hv0 i) := by
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    isSeparated_homogeneousToBase (equationIdeal p hp)
  let q : Fin n → (Spec (.of L) ⟶ hypersurface p hp) :=
    fun i => voisinDegreeTenSelectedAvoidance_normalizedCubicPointOver p hp (v i) (hpv i) (hv0 i)
  have hqbase : ∀ i, q i ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) :=
    fun i => voisinDegreeTenSelectedAvoidance_normalizedCubicPointOver_toBase p hp (v i) (hpv i) (hv0 i)
  have hqdist : ∀ i j, i ≠ j → q i ≠ q j := by
    intro i j hij heq
    exact hij (hvinj (voisinDegreeTenSelectedAvoidance_normalizedCubicPointOver_injective
      p hp (v i) (v j) (hpv i) (hpv j) (hv0 i) (hv0 j) heq))
  exact exists_orderedConfigurationFieldPoint (hypersurfaceToBase p hp) n
    (Spec.map (CommRingCat.ofHom (algebraMap K L))) q hqbase hqdist

set_option backward.isDefEq.respectTransparency false in
/-- The actual sixteen-point grid witness directly in the original cubic's
`X₀` chart. This preserves literal normalized coordinates for native relative
coefficient specialization. -/
theorem voisinDegreeTenSelectedAvoidance_exists_sixteen_grid_original_configuration
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    ∃ (v : Fin 16 → Fin 4 → L) (hv0 : ∀ i, v i 0 = 1)
      (hpv : ∀ i, p.eval₂ (algebraMap K L) (v i) = 0)
      (A : Spec (.of L) ⟶
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left),
      Function.Injective v ∧
      A ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).hom =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) ∧
      (∀ i, (A ≫ Over.Hom.left
          (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 16)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 16 i).left =
        voisinDegreeTenSelectedAvoidance_normalizedCubicPointOver p hp (v i) (hpv i) (hv0 i)) ∧
      Function.Surjective (eval₂Hom (algebraMap L (Fin 16 → L)) (fun j i => v i j)) ∧
      Function.Surjective (homogeneousSectionRestriction (K := L) (fun j i => v i j) 3) ∧
      (voisinDegreeTenSelectedAvoidance_gridCubic L 1).eval₂
        (algebraMap L (Fin 16 → L)) (fun j i => v i j) = 0 ∧
      (voisinDegreeTenSelectedAvoidance_gridCubic L 2).eval₂
        (algebraMap L (Fin 16 → L)) (fun j i => v i j) = 0 := by
  obtain ⟨v, hvinj, hv0, heval, hcubic, hpzero, hqzero, hrzero⟩ :=
    voisinDegreeTenSelectedAvoidance_exists_sixteen_grid_witness (L := L) p hp hno
  have hpv : ∀ i, p.eval₂ (algebraMap K L) (v i) = 0 := by
    intro i
    have hi := congrFun hpzero i
    rw [finite_product_evaluation_apply] at hi
    simpa [MvPolynomial.eval_map, MvPolynomial.eval₂_comp] using hi
  obtain ⟨A, hAbase, hAcoord⟩ :=
    voisinDegreeTenSelectedAvoidance_exists_ordered_configuration_over_original p hp v hvinj hpv hv0
  exact ⟨v, hv0, hpv, A, hvinj, hAbase, hAcoord, heval, hcubic, hqzero, hrzero⟩

end PfaffianDescent
