import PfaffianDescent.CorayOriginalNormalizedDirectionExplicitCut
import PfaffianDescent.GrassmannianHomogeneousFrame
import PfaffianDescent.GrassmannianChartEvaluation
import PfaffianDescent.LinearNormalizedProjectivePoint

/-! SOURCE ONLY. Any chosen ORIGINAL-K matrix in the fixed Grassmann graph
chart yields an explicit original degree-three cut/point under no-section.
Its actual AdjoinRoot normalized vector belongs to the SAME scalar-extended
graph. Whole-cut chart-j/q0/denominator/badimage avoidance is NOT asserted. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Original Fin4 coordinates of an actual fixed-chart graph column. -/
noncomputable def originalGrassmannChartLineColumn001
    {R : Type u} [CommRing R] (rho : Equiv.Perm (Fin 2 ⊕ Fin 2))
    (T : Matrix (Fin 2) (Fin 2) R) (k : Fin 2) : Fin 4 → R :=
  finiteProductCoordinateEquiv (R := R) 2 2 (grassmannianChartColumn R rho T k)

/-- Pivot labels belong to the SAME original four-coordinate numbering. -/
def originalGrassmannChartLinePivot001
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2)) (k : Fin 2) : Fin 4 :=
  finSumFinEquiv (rho (Sum.inl k))

private theorem finiteProductCoordinates_sumLabel_apply001
    {R : Type u} [CommRing R] (x : (Fin 2 → R) × (Fin 2 → R))
    (s : Fin 2 ⊕ Fin 2) :
    finiteProductCoordinateEquiv (R := R) 2 2 x (finSumFinEquiv s) =
      Sum.elim x.1 x.2 s := by
  rcases x with ⟨x₁, x₂⟩
  cases s <;>
    simp [finiteProductCoordinateEquiv, LinearEquiv.piCongrLeft,
      LinearEquiv.piCongrLeft', LinearEquiv.sumArrowLequivProdArrow,
      Equiv.sumArrowEquivProdArrow_symm_apply_inl,
      Equiv.sumArrowEquivProdArrow_symm_apply_inr]

private theorem graphCoordinatePermutation_sumLabel_apply001
    {R : Type u} [CommRing R] (rho : Equiv.Perm (Fin 2 ⊕ Fin 2))
    (x : (Fin 2 → R) × (Fin 2 → R)) (s : Fin 2 ⊕ Fin 2) :
    Sum.elim (graphCoordinatePermutation R rho x).1
      (graphCoordinatePermutation R rho x).2 s = Sum.elim x.1 x.2 (rho s) := by
  cases s <;> rfl

private theorem originalGrassmannChartLineColumn_pivot001
    {R : Type u} [CommRing R] (rho : Equiv.Perm (Fin 2 ⊕ Fin 2))
    (T : Matrix (Fin 2) (Fin 2) R) (k r : Fin 2) :
    originalGrassmannChartLineColumn001 rho T k (originalGrassmannChartLinePivot001 rho r) =
      if r = k then 1 else 0 := by
  dsimp only [originalGrassmannChartLineColumn001, originalGrassmannChartLinePivot001]
  rw [finiteProductCoordinates_sumLabel_apply001]
  dsimp only [grassmannianChartColumn]
  rw [graphCoordinatePermutation_sumLabel_apply001, rho.symm_apply_apply]
  simp [Pi.single_apply]

private theorem originalGrassmannChartLineColumn_coefficientMap001
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2)) (T : Matrix (Fin 2) (Fin 2) R) (k : Fin 2) :
    (fun i => f (originalGrassmannChartLineColumn001 rho T k i)) =
      originalGrassmannChartLineColumn001 rho (T.map f) k := by
  dsimp only [originalGrassmannChartLineColumn001]
  have h := finiteProductCoordinateEquiv_baseChange (R := R) (S := S)
    f 2 2 (grassmannianChartColumn R rho T k)
  exact h.trans (congrArg (finiteProductCoordinateEquiv (R := S) 2 2)
    (grassmannianChartColumn_map f rho T k))

/-- Every point of the explicit graph cut has its original second-pivot
coordinate one; this is the original chart condition once rho is aligned. -/
private theorem originalGrassmannChartLineRootVector_secondPivot_eq_one001
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2)) (T : Matrix (Fin 2) (Fin 2) R) (t : S) :
    (t • (fun i => f (originalGrassmannChartLineColumn001 rho T 0 i)) +
      (fun i => f (originalGrassmannChartLineColumn001 rho T 1 i)))
        (originalGrassmannChartLinePivot001 rho 1) = 1 := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [originalGrassmannChartLineColumn_pivot001, originalGrassmannChartLineColumn_pivot001]
  simp only [if_neg (show (1 : Fin 2) ≠ 0 from by decide), if_pos rfl, if_true,
    map_zero, map_one, mul_zero, zero_add]

/-- The literal scalar-extended root vector remains in the SAME actual graph,
using the accepted original column and base-change dictionaries. -/
private theorem originalGrassmannChartLineRootVector_sameGraph_membership001
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2)) (T : Matrix (Fin 2) (Fin 2) R) (t : S) :
    (finiteProductCoordinateEquiv (R := S) 2 2).symm
      (t • (fun i => f (originalGrassmannChartLineColumn001 rho T 0 i)) +
        (fun i => f (originalGrassmannChartLineColumn001 rho T 1 i))) ∈
      grassmannianChartSubmodule S rho (T.map f) := by
  rw [originalGrassmannChartLineColumn_coefficientMap001,
    originalGrassmannChartLineColumn_coefficientMap001]
  simp only [originalGrassmannChartLineColumn001, map_add, map_smul,
    LinearEquiv.symm_apply_apply]
  rw [grassmannianChartSubmodule_span]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ t (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.subset_span ⟨1, rfl⟩)

/-- A coordinate equal to one gives an actual factor of the ENTIRE named
normalized cut map through that same original coordinate chart, with exact
original coefficient map and raw normalized coordinate values. -/
private theorem explicitLinearNormalizedPoint_unitCoordinate_sameChart_factor001
    {K B : Type u} [Field K] [CommRing B] [Algebra K B]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x : Fin 4 → B) (ell : MvPolynomial (Fin 4) K) (hell : ell.IsHomogeneous 1)
    (hxell : ell.eval₂ (algebraMap K B) x = 1)
    (heI : ∀ f ∈ I.toIdeal, f.eval₂ (algebraMap K B) x = 0)
    (j : Fin 4) (hxj : x j = 1) :
    ∃ g : ChartRing I j →+* B,
      g.comp (chartBaseMap I j) = algebraMap K B ∧
      (∀ k : Fin 4, g (chartCoordinate I j k) = x k) ∧
      Spec.map (CommRingCat.ofHom g) ≫ chartι I j =
        linearNormalizedPoint I x ell hell hxell heI := by
  obtain ⟨g, hcoords, hfactor⟩ := exists_coordinateChartMap_eq_linearNormalizedPoint
    I x ell hell hxell heI j (1 : Bˣ) (by simpa only [Units.val_one] using hxj.symm)
  have hbase : g.comp (chartBaseMap I j) = algebraMap K B := by
    have ht := congrArg (fun r => r ≫ toBase I) hfactor
    rw [Category.assoc, chartι_toBase, ← Spec.map_comp, linearNormalizedPoint_toBase] at ht
    have hRing : CommRingCat.ofHom (g.comp (chartBaseMap I j)) =
        CommRingCat.ofHom (algebraMap K B) := Spec.map_injective ht
    exact congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of B => f.hom) hRing
  refine ⟨g, hbase, ?_, hfactor⟩
  intro k
  simpa only [inv_one, Units.val_one, one_mul] using hcoords k

/-- The fixed Grassmann chart can be chosen over the original coordinate
set with its second pivot equal to the prescribed ORIGINAL cubic chart. -/
theorem originalCubicChart_exists_graphPermutation_with_sameSecondPivot001
    (j : Fin 4) :
    ∃ rho : Equiv.Perm (Fin 2 ⊕ Fin 2), originalGrassmannChartLinePivot001 rho 1 = j := by
  classical
  let rho : Equiv.Perm (Fin 2 ⊕ Fin 2) :=
    Equiv.swap (Sum.inl (1 : Fin 2)) (finSumFinEquiv.symm j)
  refine ⟨rho, ?_⟩
  dsimp only [originalGrassmannChartLinePivot001, rho]
  rw [Equiv.swap_apply_left, Equiv.apply_symm_apply]

/-- Any actual ORIGINAL-K graph-chart matrix gives a literal normalized
rank-three original cubic cut and a FULL degree-three original point under
no-section. The exact root coordinates belong to SAME rho/T graph after
coefficient extension; no goodline/jet/chart-j/q0 avoidance is supplied. -/
theorem originalGrassmannChartMatrix_noSection_exists_explicit_sameGraph_rankThree_cut_and_fullDegreePoint001
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2)) (T : Matrix (Fin 2) (Fin 2) K)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    let a := originalGrassmannChartLineColumn001 rho T 0
    let b := originalGrassmannChartLineColumn001 rho T 1
    let i := originalGrassmannChartLinePivot001 rho 0
    let j := originalGrassmannChartLinePivot001 rho 1
    ∃ (c : Cubic K 4) (hc : c.toMvPolynomial = p),
    let F := cubicLinePolynomial c a b
    let B := AdjoinRoot F
    let x : Fin 4 → B :=
      AdjoinRoot.root F • (fun k => algebraMap K B (a k)) +
        (fun k => algebraMap K B (b k))
    let ell : MvPolynomial (Fin 4) K := X j - C (a j) * X i
    let I := equationIdeal p hp
    x j = 1 ∧
    (finiteProductCoordinateEquiv (R := B) 2 2).symm x ∈
      grassmannianChartSubmodule B rho (T.map (algebraMap K B)) ∧
    ∃ hBFinite : Module.Finite K B,
      letI := hBFinite
      ∃ (hell : ell.IsHomogeneous 1)
        (hxell : ell.eval₂ (algebraMap K B) x = 1)
        (heI : ∀ f ∈ I.toIdeal, f.eval₂ (algebraMap K B) x = 0),
        let r : Spec (.of B) ⟶ hypersurface p hp :=
          linearNormalizedPoint I x ell hell hxell heI
        IsClosedImmersion r ∧
        r ≫ hypersurfaceToBase p hp =
          Spec.map (CommRingCat.ofHom (algebraMap K B)) ∧
        Module.finrank K B = 3 ∧
        (∀ k : Fin 4, linearNormalizedPointChartMap I x ell hxell heI
          (linearChartCoordinate I (Ideal.Quotient.mk I.toIdeal ell)
            (polynomial_class_mem_grading I ell hell) k) = x k) ∧
        (∃ g : ChartRing I j →+* B,
          g.comp (chartBaseMap I j) = algebraMap K B ∧
          (∀ k : Fin 4, g (chartCoordinate I j k) = x k) ∧
          Spec.map (CommRingCat.ofHom g) ≫ chartι I j = r) ∧
        ∃ hFinite : IsFinite (r ≫ hypersurfaceToBase p hp),
          letI := hFinite
          finiteSchemeRank (r ≫ hypersurfaceToBase p hp) = 3 ∧
          ∃ hField : IsField B,
            letI : Field B := hField.toField
            ∃ A : closedPoints (hypersurface p hp),
              A.1 = r (IsLocalRing.closedPoint B) ∧
              IsIso (r.residueFieldMap (IsLocalRing.closedPoint B)) ∧
              (hypersurfaceToBase p hp).residueDegree A.1 = 3 := by
  classical
  intro a b i j
  obtain ⟨c, hc⟩ := homogeneous_cubic_has_tensor_any_characteristic p hp
  let F := cubicLinePolynomial c a b
  let B := AdjoinRoot F
  let x : Fin 4 → B :=
    AdjoinRoot.root F • (fun k => algebraMap K B (a k)) +
      (fun k => algebraMap K B (b k))
  let ell : MvPolynomial (Fin 4) K := X j - C (a j) * X i
  let I := equationIdeal p hp
  have hxj : x j = 1 := originalGrassmannChartLineRootVector_secondPivot_eq_one001
    (algebraMap K B) rho T (AdjoinRoot.root F)
  have hGraph : (finiteProductCoordinateEquiv (R := B) 2 2).symm x ∈
      grassmannianChartSubmodule B rho (T.map (algebraMap K B)) :=
    originalGrassmannChartLineRootVector_sameGraph_membership001
      (algebraMap K B) rho T (AdjoinRoot.root F)
  refine ⟨c, hc, hxj, hGraph, ?_⟩
  have hai : a i = 1 := by
    simpa only [a, i, if_pos rfl, if_true] using originalGrassmannChartLineColumn_pivot001 rho T 0 0
  have hbi : b i = 0 := by
    simpa only [b, i, if_neg (show (0 : Fin 2) ≠ 1 from by decide)] using
      originalGrassmannChartLineColumn_pivot001 rho T 1 0
  have hbj : b j = 1 := by
    simpa only [b, j, if_pos rfl, if_true] using originalGrassmannChartLineColumn_pivot001 rho T 1 1
  obtain ⟨hBFinite, hCut⟩ :=
    originalNormalizedDirection_noSection_explicit_rankThree_cut_and_fullDegreePoint001
      p hp c hc a b i j hai hbi hbj hno
  letI : Module.Finite K B := hBFinite
  obtain ⟨hell, hxell, heI, hClosed, hbase, hRank, hCoords, hFinite, hRest⟩ := hCut
  have hChart := explicitLinearNormalizedPoint_unitCoordinate_sameChart_factor001
    I x ell hell hxell heI j hxj
  exact ⟨hBFinite, hell, hxell, heI, hClosed, hbase, hRank, hCoords, hChart, hFinite, hRest⟩

end PfaffianDescent.Coray
