import AllCharacteristics.KollarBasechangedCenters
import AllCharacteristics.KollarUniversalSecantGenericWitness
import AllCharacteristics.KollarNormalizedPolynomialConstruction
import AllCharacteristics.ConjugateGradientTangentMatrix

/-! The normalized canonical raw family is nonzero and
detects the original cubic ideal. The geometric center callbacks are proved
using the explicit embedding into the residual root field over kbar, followed
by its algebraic closure. The two old roots remain arbitrary mapped roots;
no conjugation identity for the new field is assumed. -/

noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry HomogeneousProjective PfaffianDescent MvPolynomial Polynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Index the expanded residual Fact explicitly without changing any
reducibility attribute or the canonical root field. -/
local instance kollarRawDetector_expandedResidualFact
    {k : Type u} [Field k] (c : Cubic k 4)
    [h : Fact (Irreducible (kollarGenericResidualPolynomial c))] :
    Fact (Irreducible (Cubic.lineResidualPolynomial
      (kollarGenericMappedCubic c) (kollarGenericMappedBasePoint k)
      (kollarGenericProjectiveLineDirection k))) := by
  constructor
  change Irreducible (kollarGenericResidualPolynomial c)
  exact h.out

set_option backward.isDefEq.respectTransparency false in
/-- The large coefficient-extension construction is checked independently of
the canonical tangent matrices. It supplies both geometric callbacks for any
two old residual roots and retains their common explicit field embedding. -/
theorem exists_kollarResidual_geometric_embedding
    {k : Type u} [Field k] (c : Cubic k 4)
    (hhom : c.toMvPolynomial.IsHomogeneous 3)
    (hp : c.eval (kollarBasePoint k) = 0)
    (hsec : c.mixed (kollarBasePoint k)
      (kollarAffineLineDirection k (fun _ => 0)) ≠ 0)
    [Smooth (hypersurfaceToBase c.toMvPolynomial hhom)]
    [Fact (Irreducible (kollarGenericResidualPolynomial c))]
    (a b : AdjoinRoot (kollarGenericResidualPolynomial c))
    (ha : Polynomial.aeval a (kollarGenericResidualPolynomial c) = 0)
    (hb : Polynomial.aeval b (kollarGenericResidualPolynomial c) = 0) :
    ∃ (K : Type u) (hK : Field K),
      letI := hK
      ∃ hAC : IsAlgClosed K,
        letI := hAC
        ∃ β : AdjoinRoot (kollarGenericResidualPolynomial c) →+* K,
          GeometricallyNoContainedLineThrough
            ((c.map ((AdjoinRoot.of (kollarGenericResidualPolynomial c)).comp
              (algebraMap k (KollarGenericLineField k)))).map β)
            (fun i => β (kollarResidualLinePoint c a i)) ∧
          GeometricallyNoContainedLineThrough
            ((c.map ((AdjoinRoot.of (kollarGenericResidualPolynomial c)).comp
              (algebraMap k (KollarGenericLineField k)))).map β)
            (fun i => β (kollarResidualLinePoint c b i)) := by
  let kbar := AlgebraicClosure k
  let f : k →+* kbar := algebraMap k kbar
  letI : Smooth (hypersurfaceToBase (c.map f).toMvPolynomial
      (kollarMappedCubic_isHomogeneous f c hhom)) := kollarMappedCubic_smooth f c hhom
  letI : Fact (Irreducible (kollarGenericResidualPolynomial (c.map f))) :=
    ⟨kollarGenericResidualPolynomial_irreducible_of_smooth (c.map f)
      (kollarMappedCubic_isHomogeneous f c hhom)
      (kollarMappedCubic_basePoint_eval f c hp) (kollarMappedCubic_secant_ne_zero f c hsec)⟩
  let Lbar := AdjoinRoot (kollarGenericResidualPolynomial (c.map f))
  let K := AlgebraicClosure Lbar
  let φ : Lbar →+* K := algebraMap Lbar K
  let β := φ.comp (kollarResidualRootBaseChange f c)
  refine ⟨K, inferInstance, inferInstance, β, ?_, ?_⟩
  · exact kollar_basechanged_residual_center_geometricallyNoContainedLine_map
      f c hhom hp hsec a ha φ
  · exact kollar_basechanged_residual_center_geometricallyNoContainedLine_map
      f c hhom hp hsec b hb φ

/-- A compact property for transporting the raw family without unfolding
the two-tangent polynomial or its coefficient field. -/
def KollarRawDetectsOriginal
    {k L : Type u} [Field k] [Field L] (α : k →+* L)
    (F : MvPolynomial (Fin 4) k)
    (raw : Fin 4 → MvPolynomial ConjugateTangentParameterIndex L) : Prop :=
  let A := MvPolynomial ConjugateTangentParameterIndex L
  raw ≠ 0 ∧ ∀ (G : MvPolynomial (Fin 4) k) (d : ℕ), G.IsHomogeneous d →
    G.eval₂ ((algebraMap A (FractionRing A)).comp (MvPolynomial.C.comp α))
      (fun i => algebraMap A (FractionRing A) (raw i)) = 0 →
    G ∈ Ideal.span ({F} : Set (MvPolynomial (Fin 4) k))

set_option backward.isDefEq.respectTransparency false in
/-- The canonical conjugate tangent family is literally the family using
the solved gradient hyperplanes at both centers. This bounded equality cut
does not involve any generic target or coefficient-closure construction. -/
theorem residualLineUniversalSecantPolynomial_eq_gradient_family
    {Q : Type u} [Field Q] (c0 : Cubic Q 4) (p0 d0 : Fin 4 → Q)
    [Fact (Irreducible (Cubic.lineResidualPolynomial c0 p0 d0))]
    (σ : AdjoinRoot (Cubic.lineResidualPolynomial c0 p0 d0) ≃ₐ[Q]
      AdjoinRoot (Cubic.lineResidualPolynomial c0 p0 d0)) (j : Fin 4) :
    let L := AdjoinRoot (Cubic.lineResidualPolynomial c0 p0 d0)
    let cL := c0.map (algebraMap Q L)
    let x := residualLineRootPoint c0 p0 d0
    let y := fun i => σ (x i)
    residualLineUniversalSecantPolynomial c0 p0 d0 σ j =
      universalTwoTangentSecantPolynomial cL x y
        (hyperplaneInclusion (fun i => (MvPolynomial.pderiv i cL.toMvPolynomial).eval x) j)
        (hyperplaneInclusion (fun i => (MvPolynomial.pderiv i cL.toMvPolynomial).eval y) j)
        (AdjoinRoot.root (Cubic.lineResidualPolynomial c0 p0 d0))
        (σ (AdjoinRoot.root (Cubic.lineResidualPolynomial c0 p0 d0))) := by
  let L := AdjoinRoot (Cubic.lineResidualPolynomial c0 p0 d0)
  let cL := c0.map (algebraMap Q L)
  let x := residualLineRootPoint c0 p0 d0
  have hfixed : cL.map σ.toRingHom = cL := cubic_map_algebraMap_fixed_by_algEquiv c0 σ
  unfold residualLineUniversalSecantPolynomial residualLineTangentMatrix
  rw [hyperplaneInclusion_gradient_conjugate σ cL hfixed x j]

set_option backward.isDefEq.respectTransparency false in
theorem kollarNormalized_raw_secant_nonzero_and_detects
    {k : Type u} [Field k] (c : Cubic k 4)
    (hhom : c.toMvPolynomial.IsHomogeneous 3)
    (hp : c.eval (kollarBasePoint k) = 0)
    (hsec : c.mixed (kollarBasePoint k)
      (kollarAffineLineDirection k (fun _ => 0)) ≠ 0)
    [Smooth (hypersurfaceToBase c.toMvPolynomial hhom)]
    [Fact (Irreducible (kollarGenericResidualPolynomial c))]
    (σ : AdjoinRoot (kollarGenericResidualPolynomial c) ≃ₐ[KollarGenericLineField k]
      AdjoinRoot (kollarGenericResidualPolynomial c)) (hσ : σ ≠ AlgEquiv.refl)
    (j : Fin 4)
    (hj : (MvPolynomial.pderiv j
      ((kollarGenericMappedCubic c).map
        (algebraMap (KollarGenericLineField k)
          (AdjoinRoot (kollarGenericResidualPolynomial c)))).toMvPolynomial).eval
      (residualLineRootPoint (kollarGenericMappedCubic c) (kollarGenericMappedBasePoint k)
        (kollarGenericProjectiveLineDirection k)) ≠ 0) :
    let L := AdjoinRoot (kollarGenericResidualPolynomial c)
    let α := (algebraMap (KollarGenericLineField k) L).comp
      (algebraMap k (KollarGenericLineField k))
    let A := MvPolynomial ConjugateTangentParameterIndex L
    let raw := residualLineUniversalSecantPolynomial (kollarGenericMappedCubic c)
      (kollarGenericMappedBasePoint k) (kollarGenericProjectiveLineDirection k) σ j
    raw ≠ 0 ∧ ∀ (G : MvPolynomial (Fin 4) k) (d : ℕ), G.IsHomogeneous d →
      G.eval₂ ((algebraMap A (FractionRing A)).comp (MvPolynomial.C.comp α))
        (fun i => algebraMap A (FractionRing A) (raw i)) = 0 →
      G ∈ Ideal.span ({c.toMvPolynomial} : Set (MvPolynomial (Fin 4) k)) := by
  let Q := KollarGenericLineField k
  let c0 := kollarGenericMappedCubic c
  let p0 := kollarGenericMappedBasePoint k
  let d0 := kollarGenericProjectiveLineDirection k
  let q0 := kollarGenericResidualPolynomial c
  letI : Fact (Irreducible (Cubic.lineResidualPolynomial c0 p0 d0)) :=
    ⟨kollarGenericResidualPolynomial_irreducible_of_smooth c hhom hp hsec⟩
  let L := AdjoinRoot q0
  let α : k →+* L := (algebraMap Q L).comp (algebraMap k Q)
  let cL := c0.map (algebraMap Q L)
  let a : L := AdjoinRoot.root q0
  let b : L := σ a
  let x : Fin 4 → L := (fun i => algebraMap Q L (p0 i)) +
    a • (fun i => algebraMap Q L (d0 i))
  let y : Fin 4 → L := fun i => σ (x i)
  have hjX : (MvPolynomial.pderiv j cL.toMvPolynomial).eval x ≠ 0 := hj
  have hp0 : c0.eval p0 = 0 := by
    change (c.map (algebraMap k Q)).eval (fun i => algebraMap k Q (kollarBasePoint k i)) = 0
    rw [Cubic.eval_map, hp, map_zero]
  have hsec0 : c0.mixed p0 d0 ≠ 0 :=
    kollar_generic_projective_line_secantCoefficient_ne_zero c hsec
  have hsep0 : q0.Separable := kollarGenericResidualPolynomial_separable_of_smooth c hhom hp hsec
  have hrootA : Polynomial.aeval a q0 = 0 := by
    change Polynomial.eval₂ (algebraMap Q L) (AdjoinRoot.root q0) q0 = 0
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.eval₂_root q0
  have hrootB : Polynomial.aeval b q0 = 0 :=
    Cubic.eval₂_adjoinRoot_root_apply_algEquiv q0 σ
  have hab : a ≠ b := (Cubic.adjoinRoot_root_ne_of_algEquiv_ne_refl q0 σ hσ).symm
  have hyLine : y = (fun i => algebraMap Q L (p0 i)) +
      b • (fun i => algebraMap Q L (d0 i)) :=
    Cubic.algEquiv_linePoint p0 d0 σ a
  have hx : cL.eval x = 0 :=
    Cubic.eval_linePoint_of_lineResidual_root (algebraMap Q L) c0 p0 d0 hp0 a hrootA
  have hy : cL.eval y = 0 := by
    rw [hyLine]
    exact Cubic.eval_linePoint_of_lineResidual_root (algebraMap Q L) c0 p0 d0 hp0 b hrootB
  have hpq : cL.mixed x y ≠ 0 := by
    rw [hyLine]
    exact Cubic.mixed_distinct_linePoints_ne_zero_of_separable
      c0 p0 d0 hp0 hsec0 hsep0 b a hab.symm hrootA
  have hqp : cL.mixed y x ≠ 0 := by
    rw [hyLine]
    exact Cubic.mixed_distinct_linePoints_ne_zero_of_separable
      c0 p0 d0 hp0 hsec0 hsep0 a b hab hrootB
  obtain ⟨K, hK, hAC, β, hnoA, hnoB⟩ :=
    exists_kollarResidual_geometric_embedding c hhom hp hsec a b hrootA hrootB
  letI : Field K := hK
  letI : IsAlgClosed K := hAC
  have hnoX : GeometricallyNoContainedLineThrough ((c.map α).map β)
      (fun i => β (x i)) := hnoA
  have hnoY : GeometricallyNoContainedLineThrough ((c.map α).map β)
      (fun i => β (y i)) := by
    rw [hyLine]
    exact hnoB
  have hfixed : cL.map σ.toRingHom = cL := cubic_map_algebraMap_fixed_by_algEquiv c0 σ
  have hjY : (MvPolynomial.pderiv j cL.toMvPolynomial).eval y ≠ 0 :=
    gradient_conjugate_pivot_ne_zero σ cL hfixed x j hjX
  have hc0 : c.toMvPolynomial ≠ 0 :=
    kollar_equation_ne_zero_of_secantCoefficient_ne_zero c hsec
  have hcL : c.map α = cL := by
    funext i
    rfl
  have hxα : (c.map α).eval x = 0 := by rw [hcL]; exact hx
  have hyα : (c.map α).eval y = 0 := by rw [hcL]; exact hy
  have hpqα : (c.map α).mixed x y ≠ 0 := by rw [hcL]; exact hpq
  have hqpα : (c.map α).mixed y x ≠ 0 := by rw [hcL]; exact hqp
  have hjXα : (MvPolynomial.pderiv j (c.map α).toMvPolynomial).eval x ≠ 0 := by
    rw [hcL]
    exact hjX
  have hjYα : (MvPolynomial.pderiv j (c.map α).toMvPolynomial).eval y ≠ 0 := by
    rw [hcL]
    exact hjY
  have hw : KollarRawDetectsOriginal α c.toMvPolynomial
      (universalTwoTangentSecantPolynomial (c.map α) x y
        (hyperplaneInclusion
          (fun i => (MvPolynomial.pderiv i (c.map α).toMvPolynomial).eval x) j)
        (hyperplaneInclusion
          (fun i => (MvPolynomial.pderiv i (c.map α).toMvPolynomial).eval y) j) a b) :=
    universal_secant_generic_witness_of_geometric_centers α β c hhom hc0
      x y hxα hyα hpqα hqpα hnoX hnoY j j hjXα hjYα a b hab
  simp only [hcL] at hw
  have hxCanonical : residualLineRootPoint c0 p0 d0 = x := rfl
  have hraw := residualLineUniversalSecantPolynomial_eq_gradient_family c0 p0 d0 σ j
  dsimp only at hraw
  simp only [hxCanonical] at hraw
  change KollarRawDetectsOriginal α c.toMvPolynomial
    (residualLineUniversalSecantPolynomial c0 p0 d0 σ j)
  rw [hraw]
  exact hw


end AllCharacteristics
