import PfaffianDescent.SchemeModuleClosedPointGenericFunctionField

/-! Actual closed-point dual sections have the rational coefficient forced
by the original ideal inclusion. The punctured-open chart is the original
inclusion inverse, and the dual chart is its actual evaluation. No rational
frame, comparison or pole-image certificate is supplied.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open IdealSheafDataModule
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem canonicalIdealFrame_inclusion
    (P : closedPoints X) (U : X.Opens) (hPU : P.1 ∉ U) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    (closedImmersionModuleToUnit i).val.app (op U)
      ((schemeModuleClosedPointIdealOverCanonicalIso P U hPU).inv.val.app
        (op (Over.mk (𝟙 U))) (1 : Γ(X, U))) = (1 : Γ(X, U)) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let e := schemeModuleClosedPointIdealOverCanonicalIso P U hPU
  let T := op (Over.mk (𝟙 U))
  have h := (SchemeModuleInternalHom.overTopLinearEquiv
    (closedImmersionModule i) U e).apply_symm_apply (1 : Γ(X, U))
  change (closedImmersionModuleToUnit i).val.app (op U)
    (e.inv.val.app T (1 : Γ(X, U))) = (1 : Γ(X, U)) at h
  exact h

private theorem canonicalIdealFrame_restrict
    (P : closedPoints X) {U W : X.Opens} (f : W ⟶ U)
    (hPU : P.1 ∉ U) (hPW : P.1 ∉ W) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    M.val.map f.op
      ((schemeModuleClosedPointIdealOverCanonicalIso P U hPU).inv.val.app
        (op (Over.mk (𝟙 U))) (1 : Γ(X, U))) =
      (schemeModuleClosedPointIdealOverCanonicalIso P W hPW).inv.val.app
        (op (Over.mk (𝟙 W))) (1 : Γ(X, W)) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  let j := closedImmersionModuleToUnit i
  letI : Mono j := by
    change Mono (idealModuleToUnit i.ker)
    infer_instance
  apply SchemeModuleInternalHom.inclusion_app_injective j W
  exact (PresheafOfModules.naturality_apply j.val f.op _).trans
    ((congrArg (X.presheaf.map f.op) (canonicalIdealFrame_inclusion P U hPU)).trans
      ((map_one _).trans (canonicalIdealFrame_inclusion P W hPW).symm))

private theorem canonicalDualChart_apply
    (P : closedPoints X) (U : X.Opens) (hPU : P.1 ∉ U) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    ∀ a : (SchemeModuleInternalHom.dual M).val.obj (op U),
      SchemeModuleInternalHom.overTopLinearEquiv (SchemeModuleInternalHom.dual M) U
        (schemeModuleClosedPointDualOverCanonicalIso P U hPU) a =
      (SchemeModuleInternalHom.evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf) U
        ((schemeModuleClosedPointIdealOverCanonicalIso P U hPU).inv.val.app
          (op (Over.mk (𝟙 U))) (1 : Γ(X, U))) a : Γ(X, U)) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro a
  change (schemeModuleClosedPointDualOverCanonicalIso P U hPU).hom.val.app
    (op (Over.mk (𝟙 U))) a = _
  rw [schemeModuleClosedPointDualOverCanonicalIso_hom_val]
  rfl

private theorem canonicalDualChart_restrict
    (P : closedPoints X) {U W : X.Opens} (f : W ⟶ U)
    (hPU : P.1 ∉ U) (hPW : P.1 ∉ W) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    let D := SchemeModuleInternalHom.dual M
    ∀ a : D.val.obj (op U),
      SchemeModuleInternalHom.overTopLinearEquiv D W
        (schemeModuleClosedPointDualOverCanonicalIso P W hPW) (D.val.map f.op a) =
      X.presheaf.map f.op (SchemeModuleInternalHom.overTopLinearEquiv D U
        (schemeModuleClosedPointDualOverCanonicalIso P U hPU) a) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  let D := SchemeModuleInternalHom.dual M
  let bU := (schemeModuleClosedPointIdealOverCanonicalIso P U hPU).inv.val.app
    (op (Over.mk (𝟙 U))) (1 : Γ(X, U))
  let bW := (schemeModuleClosedPointIdealOverCanonicalIso P W hPW).inv.val.app
    (op (Over.mk (𝟙 W))) (1 : Γ(X, W))
  intro a
  have hb : M.val.map f.op bU = bW := canonicalIdealFrame_restrict P f hPU hPW
  have he : (SchemeModuleInternalHom.evaluationBilinear M O W bW
      (D.val.map f.op a) : Γ(X, W)) =
      X.presheaf.map f.op (SchemeModuleInternalHom.evaluationBilinear M O U bU a) :=
    (congrArg (fun m => SchemeModuleInternalHom.evaluationBilinear M O W m
      (D.val.map f.op a)) hb).symm.trans
        (SchemeModuleInternalHom.evaluationBilinear_restrict M O f bU a).symm
  exact (canonicalDualChart_apply P W hPW (D.val.map f.op a)).trans
    (he.trans (congrArg (X.presheaf.map f.op) (canonicalDualChart_apply P U hPU a).symm))

/-- The SAME original evaluation, with its native section carriers fixed
before specializing the scheme to a long normalization construction. -/
private def nativeDualEvaluation (M : X.Modules) (V : X.Opens)
    (m : M.val.obj (op V))
    (a : (SchemeModuleInternalHom.dual M).val.obj (op V)) : Γ(X, V) :=
  SchemeModuleInternalHom.evaluationBilinear M
    (SheafOfModules.unit X.ringCatSheaf) V m a

variable {K : Type u} [Field K] [IsIntegral X]

/-- Local ORIGINAL-K field map on the SAME actual dual, through the actual
intersection with the point complement. The map uses the existing canonical
dual chart and original section restriction, not division as a new action. -/
def schemeModuleClosedPointDualOpenToFunctionFieldLinearMap
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X) (V : X.Opens) [Nonempty V] :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    SchemeModuleOpenSectionsOver pi (SchemeModuleInternalHom.dual (closedImmersionModule i)) V →ₗ[K]
      SchemeFunctionFieldOver pi := by
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let D := SchemeModuleInternalHom.dual (closedImmersionModule i)
  let W := V ⊓ schemeClosedPointComplementOpen P
  have hgV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using (inferInstance : Nonempty V))
  have hgW : genericPoint X ∈ W :=
    ⟨hgV, schemeClosedPoint_generic_mem_complement P hP⟩
  have hPW : P.1 ∉ W := fun h => schemeClosedPoint_not_mem_complement P h.2
  letI : Nonempty W := ⟨⟨genericPoint X, hgW⟩⟩
  exact (schemeModuleChartSectionsToFunctionFieldLinearMap pi D W
    (schemeModuleClosedPointDualOverCanonicalIso P W hPW)).comp
      (schemeModuleOpenSectionsRestrictionLinearMap pi D (show W ≤ V from inf_le_left))

/-- Actual numerator identity for EVERY local ideal section m and dual
section a. No generator, nonzero-denominator or comparison premise is used. -/
theorem schemeModuleClosedPointDualOpenToFunctionFieldLinearMap_mul_frame
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X) (V : X.Opens) [Nonempty V] :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    ∀ (m : M.val.obj (op V))
      (a : SchemeModuleOpenSectionsOver pi (SchemeModuleInternalHom.dual M) V),
      @HMul.hMul X.functionField X.functionField X.functionField inferInstance
        (schemeModuleClosedPointDualOpenToFunctionFieldLinearMap pi P hP V a)
        (X.germToFunctionField V ((closedImmersionModuleToUnit i).val.app (op V) m)) =
        X.germToFunctionField V
          (SchemeModuleInternalHom.evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf) V m a) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  let j := closedImmersionModuleToUnit i
  let D := SchemeModuleInternalHom.dual M
  let W := V ⊓ schemeClosedPointComplementOpen P
  let f : W ⟶ V := homOfLE inf_le_left
  have hgV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using (inferInstance : Nonempty V))
  have hgW : genericPoint X ∈ W :=
    ⟨hgV, schemeClosedPoint_generic_mem_complement P hP⟩
  have hPW : P.1 ∉ W := fun h => schemeClosedPoint_not_mem_complement P h.2
  letI : Nonempty W := ⟨⟨genericPoint X, hgW⟩⟩
  letI : Mono j := by
    change Mono (idealModuleToUnit i.ker)
    infer_instance
  let b := (schemeModuleClosedPointIdealOverCanonicalIso P W hPW).inv.val.app
    (op (Over.mk (𝟙 W))) (1 : Γ(X, W))
  let q := SchemeModuleInternalHom.overTopLinearEquiv D W
    (schemeModuleClosedPointDualOverCanonicalIso P W hPW)
  intro m a
  let z : Γ(X, V) := j.val.app (op V) m
  let zW : Γ(X, W) := X.presheaf.map f.op z
  let aW := D.val.map f.op a
  let F : M.val.obj (op W) →ₗ[Γ(X, W)] Γ(X, W) :=
    (SchemeModuleInternalHom.evaluationBilinear M O W).flip aW
  have hm : M.val.map f.op m = zW • b := by
    apply SchemeModuleInternalHom.inclusion_app_injective j W
    calc
      j.val.app (op W) (M.val.map f.op m) = zW :=
        PresheafOfModules.naturality_apply j.val f.op m
      _ = zW * (1 : Γ(X, W)) := (mul_one zW).symm
      _ = zW • (j.val.app (op W) b : Γ(X, W)) :=
        congrArg (fun c : Γ(X, W) => zW • c) (canonicalIdealFrame_inclusion P W hPW).symm
      _ = j.val.app (op W) (zW • b) := ((j.val.app (op W)).hom.map_smul zW b).symm
  have he : X.presheaf.map f.op (SchemeModuleInternalHom.evaluationBilinear M O V m a) =
      zW * F b :=
    (SchemeModuleInternalHom.evaluationBilinear_restrict M O f m a).trans
      ((congrArg F hm).trans (F.map_smul zW b))
  have hq : q aW = F b := canonicalDualChart_apply P W hPW aW
  have hlocal : X.presheaf.map f.op (SchemeModuleInternalHom.evaluationBilinear M O V m a) =
      zW * q aW := he.trans (congrArg (fun c : Γ(X, W) => zW * c) hq).symm
  have hres (r : Γ(X, V)) :
      X.germToFunctionField W (X.presheaf.map f.op r) = X.germToFunctionField V r :=
    X.presheaf.germ_res_apply f (genericPoint X) hgW r
  change X.germToFunctionField W (q aW) * X.germToFunctionField V z = _
  calc
    _ = X.germToFunctionField W (q aW) * X.germToFunctionField W zW :=
      congrArg (fun c : X.functionField => X.germToFunctionField W (q aW) * c) (hres z).symm
    _ = X.germToFunctionField W (zW * q aW) :=
      (mul_comm _ _).trans (map_mul (X.germToFunctionField W).hom zW (q aW)).symm
    _ = X.germToFunctionField W
        (X.presheaf.map f.op (SchemeModuleInternalHom.evaluationBilinear M O V m a)) :=
      congrArg (X.germToFunctionField W) hlocal.symm
    _ = X.germToFunctionField V (SchemeModuleInternalHom.evaluationBilinear M O V m a) := hres _

/-- Genuine fraction formula. A nonzero original frame inclusion is the
only additional algebraic input; the primitive caller derives it below. -/
theorem schemeModuleClosedPointDualOpenToFunctionFieldLinearMap_eq_fraction
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X) (V : X.Opens) [Nonempty V] :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    ∀ (m : M.val.obj (op V))
      (hz : ((closedImmersionModuleToUnit i).val.app (op V) m : Γ(X, V)) ≠ 0)
      (a : SchemeModuleOpenSectionsOver pi (SchemeModuleInternalHom.dual M) V),
      (schemeModuleClosedPointDualOpenToFunctionFieldLinearMap pi P hP V a : X.functionField) =
        X.germToFunctionField V
          (SchemeModuleInternalHom.evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf) V m a) /
        X.germToFunctionField V ((closedImmersionModuleToUnit i).val.app (op V) m) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro m hz a
  have hden : X.germToFunctionField V ((closedImmersionModuleToUnit i).val.app (op V) m) ≠ 0 := by
    intro hzero
    apply hz
    apply X.germToFunctionField_injective V
    exact hzero.trans (map_zero (X.germToFunctionField V).hom).symm
  exact (eq_div_iff hden).mpr
    (schemeModuleClosedPointDualOpenToFunctionFieldLinearMap_mul_frame pi P hP V m a)

/-- The local construction is the SAME existing global field map on
restricted global sections. Canonical inclusion inverses supply all frame
coherence internally; no field-map comparison is a premise. -/
theorem schemeModuleClosedPointDualOpenToFunctionFieldLinearMap_restrict_global
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X) (V : X.Opens) [Nonempty V] :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let D := SchemeModuleInternalHom.dual (closedImmersionModule i)
    ∀ a : SchemeModuleOpenSectionsOver pi D ⊤,
      schemeModuleClosedPointDualOpenToFunctionFieldLinearMap pi P hP V
        (D.val.map (homOfLE (show V ≤ ⊤ from le_top)).op a) =
      schemeModuleClosedPointDualToFunctionFieldLinearMap pi P hP a := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let D := SchemeModuleInternalHom.dual (closedImmersionModule i)
  let U := schemeClosedPointComplementOpen P
  let W := V ⊓ U
  have hgU : genericPoint X ∈ U := schemeClosedPoint_generic_mem_complement P hP
  have hgV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using (inferInstance : Nonempty V))
  have hgW : genericPoint X ∈ W := ⟨hgV, hgU⟩
  have hPU : P.1 ∉ U := schemeClosedPoint_not_mem_complement P
  have hPW : P.1 ∉ W := fun h => hPU h.2
  letI : Nonempty U := ⟨⟨genericPoint X, hgU⟩⟩
  letI : Nonempty W := ⟨⟨genericPoint X, hgW⟩⟩
  let f : W ⟶ U := homOfLE inf_le_right
  let g : W ⟶ V := homOfLE inf_le_left
  let qU := SchemeModuleInternalHom.overTopLinearEquiv D U
    (schemeModuleClosedPointDualOverCanonicalIso P U hPU)
  let qW := SchemeModuleInternalHom.overTopLinearEquiv D W
    (schemeModuleClosedPointDualOverCanonicalIso P W hPW)
  intro a
  let aU := D.val.map (homOfLE (show U ≤ ⊤ from le_top)).op a
  let aV := D.val.map (homOfLE (show V ≤ ⊤ from le_top)).op a
  have hrestrict (A : X.Opens) (k : W ⟶ A) :
      D.val.map k.op (D.val.map (homOfLE (show A ≤ ⊤ from le_top)).op a) =
        D.val.map (homOfLE (show W ≤ ⊤ from le_top)).op a := by
    exact (D.val.map_comp_apply (homOfLE (show A ≤ ⊤ from le_top)).op k.op a).symm.trans
      (congrArg (fun t => D.val.map t a) (Subsingleton.elim _ _))
  have hs : D.val.map g.op aV = D.val.map f.op aU :=
    (hrestrict V g).trans (hrestrict U f).symm
  have hc : qW (D.val.map f.op aU) = X.presheaf.map f.op (qU aU) :=
    canonicalDualChart_restrict P f hPU hPW aU
  change X.germToFunctionField W (qW (D.val.map g.op aV)) =
    X.germToFunctionField U (qU aU)
  exact (congrArg (fun s => X.germToFunctionField W (qW s)) hs).trans
    ((congrArg (X.germToFunctionField W) hc).trans
      (X.presheaf.germ_res_apply f (genericPoint X) hgW (qU aU)))

/-- Ordinary integral-scheme witness construction. Its hypothesis is an
actual regular affine ideal generator; it does not supply a rational formula. -/
private theorem closedPointDual_fraction_chart_of_regularGenerator
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X)
    (hgen :
      let i := X.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let M := (show X.Modules from closedImmersionModule i)
      ∃ V : X.affineOpens, P.1 ∈ V.1 ∧
        ∃ m : M.val.presheaf.obj (op V.1),
          let z : Γ(X, V.1) := (closedImmersionModuleToUnit i).val.app (op V.1) m
          IsRegular z ∧ i.ker.ideal V = Ideal.span ({z} : Set Γ(X, V.1))) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    ∃ (V : X.affineOpens) (hPV : P.1 ∈ V.1),
      letI : Nonempty V.1 := ⟨⟨P.1, hPV⟩⟩
      ∃ m : M.val.obj (op V.1),
        let z : Γ(X, V.1) := (closedImmersionModuleToUnit i).val.app (op V.1) m
        IsRegular z ∧ i.ker.ideal V = Ideal.span ({z} : Set Γ(X, V.1)) ∧
        ∀ a : SchemeModuleOpenSectionsOver pi (SchemeModuleInternalHom.dual M) V.1,
          (schemeModuleClosedPointDualOpenToFunctionFieldLinearMap pi P hP V.1 a :
            X.functionField) =
            X.germToFunctionField V.1 (nativeDualEvaluation M V.1 m a) /
              X.germToFunctionField V.1 z := by
  dsimp only at hgen ⊢
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  obtain ⟨V, hPV, m, hreg, hprincipal⟩ := hgen
  letI : Nonempty V.1 := ⟨⟨P.1, hPV⟩⟩
  refine ⟨V, hPV, m, hreg, hprincipal, ?_⟩
  intro a
  exact schemeModuleClosedPointDualOpenToFunctionFieldLinearMap_eq_fraction pi P hP V.1 m
    (isRegular_iff_ne_zero.mp hreg) a

end PfaffianDescent

namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective IdealSheafDataModule
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Primitive SAME normalization: internally chosen actual affine ideal
generator yields the actual local dual fraction formula. No chart, nonzero
denominator, rational frame or field comparison certificate is supplied. -/
theorem projectiveIntersection_genericNormalization_closedPoint_dual_fraction_chart
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase I
    ∀ P : closedPoints N,
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let M := (show N.Modules from closedImmersionModule i)
      ∃ (V : N.affineOpens) (hPV : P.1 ∈ V.1),
        letI : Nonempty V.1 := ⟨⟨P.1, hPV⟩⟩
        ∃ m : M.val.obj (op V.1),
          let z : Γ(N, V.1) := (closedImmersionModuleToUnit i).val.app (op V.1) m
          IsRegular z ∧ i.ker.ideal V = Ideal.span ({z} : Set Γ(N, V.1)) ∧
          ∀ a : SchemeModuleOpenSectionsOver pi (SchemeModuleInternalHom.dual M) V.1,
            (schemeModuleClosedPointDualOpenToFunctionFieldLinearMap pi P
              (projectiveIntersection_genericNormalization_closedPoint_ne_generic p q hp hq P) V.1 a :
                N.functionField) =
              N.germToFunctionField V.1
                (nativeDualEvaluation M V.1 m a) /
              N.germToFunctionField V.1 z := by
  classical
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase I
  intro P
  exact closedPointDual_fraction_chart_of_regularGenerator pi P
    (projectiveIntersection_genericNormalization_closedPoint_ne_generic p q hp hq P)
    (projectiveIntersection_genericNormalization_closedPoint_ideal_affine_regularGenerator
      p q hp hp0 n hn hq hnot P)

end PfaffianDescent.Coray
