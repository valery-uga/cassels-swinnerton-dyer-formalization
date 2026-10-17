import Lean
import Lean.Meta.Tactic.Delta
import PfaffianDescent.ActualRestrictedIdealTwistLocalBasisAction
import PfaffianDescent.ActualClosedIdealSourceRestrictionIso
import PfaffianDescent.ActualOriginalNativeIdealTwistChartIso
import PfaffianDescent.ActualOriginalPositiveTwoLocalBasisCoefficient

/- SOURCE ONLY / UNVERIFIED. The SAME original ideal-twist local
basis generator maps to the SAME actual untwisted ideal generator under
native chart refinement. All inclusion/basis/factorization laws derived. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite IdealSheafDataModule
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def actualOriginalNativeUntwistedIdealChartIso
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let q := (hypersurface p hp).fromSpecResidueField P.1
    (Scheme.Modules.restrictFunctor (chartι (equationIdeal p hp) C.index)).obj
      (closedImmersionModule q) ≅
      closedImmersionModule (Spec.map (CommRingCat.ofHom C.residue)) := by
  dsimp only
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom C.residue)) :=
    IsClosedImmersion.spec_of_surjective _ C.residue_surjective
  exact (actualOriginalNativeIdealTwistConstructedChartData p hp P C).untwistedIso

-- Every concrete Iso below is a projection of the SAME original package.
-- No defining HEq between independently reconstructed factory terms is input.
attribute [local irreducible] actualOriginalNativeIdealTwistConstructedChartData

attribute [local irreducible] actualOriginalQuarticCotangentChartChoice

/-- The local equation is formed once at abstract schemes, without any
original chart, residue-field presentation or public factory aliases.
The two closed immersions have independent sources: the equation only
uses their ideal modules on X and Y, and does not require a factorization. -/
private def actualIdealChartLocalBasisLaw
    {X Y Z W : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (q : Z ⟶ X) [IsClosedImmersion q]
    (j : W ⟶ Y) [IsClosedImmersion j] (T : X.Modules)
    (e : (Scheme.Modules.restrictFunctor f).obj
      (closedImmersionIdealTwist q T) ≅ closedImmersionModule j)
    (n : (Scheme.Modules.restrictFunctor f).obj
      (closedImmersionModule q) ≅ closedImmersionModule j)
    (b : ∀ U : X.Opens, T.val.obj (op U)) : Prop :=
  ∀ (U : X.Opens) (m : (closedImmersionModule q).val.obj (op U)),
    e.hom.val.app (op (f ⁻¹ᵁ U))
      (((Scheme.Modules.restrictAdjunction f).unit.app
        (schemeModuleTensor (closedImmersionModule q) T)).val.app (op U)
        (actualModuleLocalTensorSection (closedImmersionModule q) T U m (b U))) =
    n.hom.val.app (op (f ⁻¹ᵁ U))
      (((Scheme.Modules.restrictAdjunction f).unit.app
        (closedImmersionModule q)).val.app (op U) m)

/- Expand the local equation while every scheme and map is abstract. -/
private theorem actualIdealChartLocalBasisLaw_explicit
    {X Y Z W : Scheme.{u}} {f : Y ⟶ X} [IsOpenImmersion f]
    {q : Z ⟶ X} [IsClosedImmersion q]
    {j : W ⟶ Y} [IsClosedImmersion j] {T : X.Modules}
    {e : (Scheme.Modules.restrictFunctor f).obj
      (closedImmersionIdealTwist q T) ≅ closedImmersionModule j}
    {n : (Scheme.Modules.restrictFunctor f).obj
      (closedImmersionModule q) ≅ closedImmersionModule j}
    {b : ∀ U : X.Opens, T.val.obj (op U)}
    (h : actualIdealChartLocalBasisLaw f q j T e n b) :
  ∀ (U : X.Opens) (m : (closedImmersionModule q).val.obj (op U)),
    e.hom.val.app (op (f ⁻¹ᵁ U))
      (((Scheme.Modules.restrictAdjunction f).unit.app
        (schemeModuleTensor (closedImmersionModule q) T)).val.app (op U)
        (actualModuleLocalTensorSection (closedImmersionModule q) T U m (b U))) =
    n.hom.val.app (op (f ⁻¹ᵁ U))
      (((Scheme.Modules.restrictAdjunction f).unit.app
        (closedImmersionModule q)).val.app (op U) m) := by
  exact h

/-- Read the SAME package action as the named local-law predicate while
all schemes, Isos and basis maps remain abstract. No concrete equation or
residue-field presentation is converted at the original supplied chart. -/
private theorem actualIdealChartLocalBasisLaw_of_data
    {X Y Z : Scheme.{u}} {U0 : X.Opens}
    {f : Y ⟶ (U0 : Scheme)} [IsIso f]
    {f0 : Y ⟶ X} [IsOpenImmersion f0] {hF : f0 = f ≫ U0.ι}
    {q : Z ⟶ X} [IsClosedImmersion q]
    {j : Z ⟶ Y} [IsClosedImmersion j]
    {hfac : (j ≫ f) ≫ U0.ι = q} {T : X.Modules}
    {p0 : (Scheme.Modules.restrictFunctor U0.ι).obj T ≅
      SheafOfModules.unit (U0 : Scheme).ringCatSheaf}
    (D : ActualNamedIdealTwistChartData U0 f f0 hF q j hfac T p0)
    (v : schemeModuleUnit X ⟶ T)
    (hb : (Scheme.Modules.restrictFunctor (f ≫ U0.ι)).map v ≫
      (cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U0 f T p0).hom =
        (Scheme.Modules.restrictUnitIso (f ≫ U0.ι)).hom) :
    actualIdealChartLocalBasisLaw (W := Z) f0 q j T D.idealIso D.untwistedIso
      (fun U => T.val.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (v.val.app (op ⊤) (1 : Γ(X, ⊤)))) := by
  exact D.localBasisAction v hb

universe v w x

/-- Transfer a predicate through separately proved whole-value equalities.
All three parameter types and the predicate remain abstract here. -/
private theorem actualLocalLaw_transfer
    {A : Sort v} {B : Sort w} {C : Sort x}
    (L : A → B → C → Prop)
    {a a' : A} {b b' : B} {c c' : C}
    (ha : a = a') (hb : b = b') (hc : c = c')
    (h : L a' b' c') : L a b c := by
  cases ha
  cases hb
  cases hc
  exact h

/-- Whole ideal Iso fidelity is checked separately from any local action.
The original producer returns exactly this same package projection. -/
private lemma actualOriginalIdealChartIso_eq_package
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom C.residue)) :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    (actualOriginalNativeIdealTwistChartIso p hp P hP) =
      (actualOriginalNativeIdealTwistConstructedChartData p hp P C).idealIso := by
  dsimp only
  rfl

/-- Whole untwisted Iso fidelity is checked separately. This preserves
its inverse as well as its hom and its original source factorization. -/
private lemma actualOriginalUntwistedChartIso_eq_package
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom C.residue)) :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    (actualOriginalNativeUntwistedIdealChartIso p hp P hP) =
      (actualOriginalNativeIdealTwistConstructedChartData p hp P C).untwistedIso := by
  dsimp only
  rfl

/-- The complete public local basis FUNCTION is the restriction of the
same original coordinate-square basis morphism. No coefficient is input. -/
private lemma actualOriginalLocalBasisFunction_eq_restriction
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let T := positiveSheafOfModules (grading I) 2
    let ell : grading I 1 := ⟨coordinate I C.index, coordinate_mem I C.index⟩
    let v := actualPositiveTwistChartBasisInvHom I ell 2
    actualOriginalPositiveTwoLocalBasisSection p hp P hP =
      fun U => T.val.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (v.val.app (op ⊤) (1 : Γ(hypersurface p hp, ⊤))) := by
  dsimp only
  rfl

/-- Specialize the already predicate-valued package law to the SAME
original supplied chart, keeping the original hypersurface domain explicit. -/
private def actualConstructedIdealChartPredicateProofValue
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) := by
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let j := Spec.map (CommRingCat.ofHom C.residue)
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
  letI : IsOpenImmersion (chartι I C.index) := isOpenImmersion_chartι I C.index
  let T := positiveSheafOfModules (grading I) 2
  let ell : grading I 1 := ⟨coordinate I C.index, coordinate_mem I C.index⟩
  let v := actualPositiveTwistChartBasisInvHom I ell 2
  let D := actualOriginalNativeIdealTwistConstructedChartData p hp P C
  exact actualIdealChartLocalBasisLaw_of_data
    (X := hypersurface p hp) D v
    (actualPositiveTwistRefinedChartUnitIso_basis I C.index 2)

private opaque actualConstructedIdealChartPredicateProof
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    type_of% (actualConstructedIdealChartPredicateProofValue p hp P C) :=
  actualConstructedIdealChartPredicateProofValue p hp P C

/- Fix the SAME named predicate, complete original Isos and complete
basis functions before any whole-value equality or predicate proof is supplied.
The remaining arguments are precisely the three proved equalities and raw law. -/
set_option backward.isDefEq.respectTransparency false in
private def actualOriginalLocalLawTransferCriterionValue
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let j := Spec.map (CommRingCat.ofHom C.residue)
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
  letI : IsOpenImmersion (chartι I C.index) := isOpenImmersion_chartι I C.index
  let T := positiveSheafOfModules (grading I) 2
  let ell : grading I 1 := ⟨coordinate I C.index, coordinate_mem I C.index⟩
  let v := actualPositiveTwistChartBasisInvHom I ell 2
  let b := fun U => T.val.map (homOfLE (show U ≤ ⊤ from le_top)).op
    (v.val.app (op ⊤) (1 : Γ(hypersurface p hp, ⊤)))
  let D := actualOriginalNativeIdealTwistConstructedChartData p hp P C
  exact actualLocalLaw_transfer
    (actualIdealChartLocalBasisLaw (X := hypersurface p hp) (chartι I C.index) q j T)
    (a := actualOriginalNativeIdealTwistChartIso p hp P hP) (a' := D.idealIso)
    (b := actualOriginalNativeUntwistedIdealChartIso p hp P hP) (b' := D.untwistedIso)
    (c := actualOriginalPositiveTwoLocalBasisSection p hp P hP) (c' := b)

set_option backward.isDefEq.respectTransparency true in
private opaque actualOriginalLocalLawTransferCriterion
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    type_of% (actualOriginalLocalLawTransferCriterionValue p hp P hP) :=
  actualOriginalLocalLawTransferCriterionValue p hp P hP

/- The first continuation supplies only the independently proved whole ideal Iso equality. -/
set_option backward.isDefEq.respectTransparency true in
private def actualOriginalLocalLawAfterIdealIsoValue
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :=
  actualOriginalLocalLawTransferCriterion p hp P hP
    (actualOriginalIdealChartIso_eq_package p hp P hP)

set_option backward.isDefEq.respectTransparency true in
private opaque actualOriginalLocalLawAfterIdealIso
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    type_of% (actualOriginalLocalLawAfterIdealIsoValue p hp P hP) :=
  actualOriginalLocalLawAfterIdealIsoValue p hp P hP

/- The second continuation supplies only the independently proved whole untwisted Iso equality. -/
set_option backward.isDefEq.respectTransparency true in
private def actualOriginalLocalLawAfterUntwistedIsoValue
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :=
  actualOriginalLocalLawAfterIdealIso p hp P hP
    (actualOriginalUntwistedChartIso_eq_package p hp P hP)

set_option backward.isDefEq.respectTransparency true in
private opaque actualOriginalLocalLawAfterUntwistedIso
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    type_of% (actualOriginalLocalLawAfterUntwistedIsoValue p hp P hP) :=
  actualOriginalLocalLawAfterUntwistedIsoValue p hp P hP

/- The third continuation supplies only the independently proved complete basis function equality. -/
set_option backward.isDefEq.respectTransparency true in
private def actualOriginalLocalLawAfterBasisFunctionValue
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :=
  actualOriginalLocalLawAfterUntwistedIso p hp P hP
    (actualOriginalLocalBasisFunction_eq_restriction p hp P hP)

set_option backward.isDefEq.respectTransparency true in
private opaque actualOriginalLocalLawAfterBasisFunction
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    type_of% (actualOriginalLocalLawAfterBasisFunctionValue p hp P hP) :=
  actualOriginalLocalLawAfterBasisFunctionValue p hp P hP

/- Only the already proved SAME supplied-chart predicate remains.
No concrete map or whole-value equality is reconstructed at this application. -/
set_option backward.isDefEq.respectTransparency true in
private def actualOriginalPublicIdealLocalBasisLawProofValue
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :=
  actualOriginalLocalLawAfterBasisFunction p hp P hP
    (actualConstructedIdealChartPredicateProof p hp P
      (actualOriginalQuarticCotangentChartChoice p hp P hP))

/-- Full proof body is supplied above. The inferred type retains all
three PUBLIC factory symbols, rather than the raw package projections. -/
private opaque actualOriginalPublicIdealLocalBasisLawProof
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    type_of% (actualOriginalPublicIdealLocalBasisLawProofValue p hp P hP) :=
  actualOriginalPublicIdealLocalBasisLawProofValue p hp P hP


end PfaffianDescent
end

namespace CasselsStructuralCertificate081

universe u v

/-- Congruence for dependent function types with separate domains. -/
private theorem pi_eq
    {A A' : Sort u} (B : A → Sort v) (B' : A' → Sort v)
    (hA : A = A')
    (hB : ∀ a a', HEq a a' → B a = B' a') :
    (∀ a, B a) = (∀ a', B' a') := by
  cases hA
  have h : B = B' := funext fun a => hB a a (HEq.refl a)
  cases h
  rfl

/-- Congruence for functions with separate domains and dependent ranges. -/
private theorem lambda_heq
    {A A' : Sort u} {B : A → Sort v} {B' : A' → Sort v}
    (f : ∀ a, B a) (f' : ∀ a', B' a')
    (hA : A = A')
    (hB : ∀ a a', HEq a a' → B a = B' a')
    (hf : ∀ a a', HEq a a' → HEq (f a) (f' a')) : HEq f f' := by
  cases hA
  have h : B = B' := funext fun a => hB a a (HEq.refl a)
  cases h
  exact heq_of_eq (funext fun a => eq_of_heq (hf a a (HEq.refl a)))

end CasselsStructuralCertificate081

meta section
namespace CasselsStructuralCertificate081
open Lean Meta Elab Tactic

private def isLocalLawName (n : Name) : Bool :=
  match n with
  | .str _ s => s == "actualIdealChartLocalBasisLaw"
  | _ => false

/-- Only the already diagnosed predicate and identity/scheme aliases are
expanded. Native factories, choice and residue wrappers stay opaque. -/
private partial def normalizeHead (e : Expr) (fuel : Nat) : MetaM Expr := do
  let e := e.consumeMData.headBeta
  if fuel == 0 then return e
  if let .letE _ _ val body _ := e then
    return ← normalizeHead (body.instantiate1 val) (fuel - 1)
  let allowed := match e.getAppFn with
    | .const n _ => isLocalLawName n ||
      n == ``AllCharacteristics.HomogeneousProjective.hypersurface || n == ``id
    | _ => false
  if !allowed then return e
  let some e' ← delta? e (fun n => isLocalLawName n ||
    n == ``AllCharacteristics.HomogeneousProjective.hypersurface || n == ``id)
    | return e
  normalizeHead e' (fuel - 1)

/-- Turn a projection head into its declared projection function. No value
of the projected structure is unfolded. -/
private def projectionAsApplication (e : Expr) : MetaM Expr := do
  let .proj structName idx major := e.getAppFn | return e
  let some info := getStructureInfo? (← getEnv) structName
    | throwError "Structural081 cannot recover structure metadata for {structName}."
  let some projName := info.getProjFn? idx
    | throwError "Structural081 cannot recover projection {structName}[{idx}]."
  let ty ← whnfD (← inferType major)
  let .const typeName levels := ty.getAppFn
    | throwError "Structural081 projection source has no structure type."
  unless typeName == structName do
    throwError "Structural081 projection source structure differs: {structName} / {typeName}."
  let .inductInfo ind ← getConstInfo structName
    | throwError "Structural081 projection source is not inductive."
  let params := ty.getAppArgs.extract 0 ind.numParams
  return mkAppN (mkApp (mkAppN (mkConst projName levels) params) major) e.getAppArgs

private structure CertificateState where
  remaining : Nat := 1024
  pairs : Array (Expr × Expr × Expr) := #[]
  congruences : Array (Expr × Nat × CongrTheorem) := #[]
  proofLeaves : Nat := 0
  congrSteps : Nat := 0
  binderSteps : Nat := 0

private abbrev CertificateM := StateT CertificateState MetaM

private def cache (left right certificate : Expr) : CertificateM Expr := do
  modify fun s => { s with pairs := s.pairs.push (left, right, certificate) }
  return certificate

private def congruenceFor (head : Expr) (arity : Nat) : CertificateM CongrTheorem := do
  if let some (_, _, thm) := (← get).congruences.find? fun (f, n, _) =>
      f.equal head && n == arity then
    return thm
  let thm ← mkHCongrWithArity head arity
  modify fun s => { s with congruences := s.congruences.push (head, arity, thm) }
  return thm

/-- Each nontrivial step has a proof: a proof_irrel_heq leaf, a generated
abstract congruence lambda, or the ordinary pi/lambda theorem above.
Generated congruence lambdas are part of the final kernel checked term. -/
private partial def structuralHEq (left0 right0 : Expr) (depth : Nat)
    (locals : Array (Expr × Expr × Expr)) : CertificateM Expr := do
  if left0.equal right0 then return ← mkHEqRefl left0
  if let some (_, _, h) := locals.find? fun (l, r, _) =>
      l.equal left0 && r.equal right0 then
    return h
  if let some (_, _, h) := (← get).pairs.find? fun (l, r, _) =>
      l.equal left0 && r.equal right0 then
    return h
  if depth == 0 || (← get).remaining == 0 then
    throwError "Structural081 certificate traversal exhausted its explicit bound."
  modify fun s => { s with remaining := s.remaining - 1 }
  let left ← normalizeHead left0 8
  let right ← normalizeHead right0 8
  if left.equal right then return ← cache left0 right0 (← mkHEqRefl left)
  let lp ← isProofQuick left
  let rp ← isProofQuick right
  if lp == .true && rp == .true then
    let p ← inferType left
    let q ← inferType right
    let h := mkAppN (mkConst ``proof_irrel_heq) #[p, q, left, right]
    modify fun s => { s with proofLeaves := s.proofLeaves + 1 }
    return ← cache left0 right0 h
  match left, right with
  | .forallE n A B bi, .forallE _ A' B' _ =>
    let hA ← mkEqOfHEq (← structuralHEq A A' (depth - 1) locals)
    let u ← getLevel A
    let leftFamily ← withLocalDecl n bi A fun a => do
      mkLambdaFVars #[a] (B.instantiate1 a)
    let rightFamily ← withLocalDecl n bi A' fun a' => do
      mkLambdaFVars #[a'] (B'.instantiate1 a')
    let v ← withLocalDecl n bi A fun a => getLevel (B.instantiate1 a)
    let hB ← withLocalDecl n bi A fun a => do
      withLocalDecl (n.appendAfter "'") bi A' fun a' => do
        withLocalDeclD `h (← mkHEq a a') fun h => do
          let bodyEq ← mkEqOfHEq (← structuralHEq
            (B.instantiate1 a) (B'.instantiate1 a') (depth - 1)
            (locals.push (a, a', h)))
          mkLambdaFVars #[a, a', h] bodyEq
    let eq := mkAppN (mkConst ``pi_eq [u, v])
      #[A, A', leftFamily, rightFamily, hA, hB]
    modify fun s => { s with binderSteps := s.binderSteps + 1 }
    return ← cache left0 right0 (← mkHEqOfEq eq)
  | .lam n A body bi, .lam _ A' body' _ =>
    let hA ← mkEqOfHEq (← structuralHEq A A' (depth - 1) locals)
    let u ← getLevel A
    let B ← withLocalDecl n bi A fun a => do
      mkLambdaFVars #[a] (← inferType (body.instantiate1 a))
    let B' ← withLocalDecl n bi A' fun a' => do
      mkLambdaFVars #[a'] (← inferType (body'.instantiate1 a'))
    let v ← withLocalDecl n bi A fun a => do getLevel (← inferType (body.instantiate1 a))
    let (hB, hf) ← withLocalDecl n bi A fun a => do
      withLocalDecl (n.appendAfter "'") bi A' fun a' => do
        withLocalDeclD `h (← mkHEq a a') fun h => do
          let l := body.instantiate1 a
          let r := body'.instantiate1 a'
          let locals := locals.push (a, a', h)
          let typeEq ← mkEqOfHEq (← structuralHEq (← inferType l) (← inferType r)
            (depth - 1) locals)
          let valueHEq ← structuralHEq l r (depth - 1) locals
          return (← mkLambdaFVars #[a, a', h] typeEq,
            ← mkLambdaFVars #[a, a', h] valueHEq)
    let h := mkAppN (mkConst ``lambda_heq [u, v])
      #[A, A', B, B', left, right, hA, hB, hf]
    modify fun s => { s with binderSteps := s.binderSteps + 1 }
    return ← cache left0 right0 h
  | _, _ => pure ()
  let left ← projectionAsApplication left
  let right ← projectionAsApplication right
  let lh := left.getAppFn
  let rh := right.getAppFn
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless lh.equal rh && la.size == ra.size && !la.isEmpty do
    throwError "Structural081 found an unsupported non-proof head boundary."
  let thm ← congruenceFor lh la.size
  let mut args := #[]
  for i in [:la.size] do
    let h ← structuralHEq la[i]! ra[i]! (depth - 1) locals
    let h ← match thm.argKinds[i]! with
      | .eq => mkEqOfHEq h
      | .heq => pure h
      | _ => throwError "Structural081 unexpected abstract congruence argument kind."
    args := args ++ #[la[i]!, ra[i]!, h]
  modify fun s => { s with congrSteps := s.congrSteps + 1 }
  cache left0 right0 (mkAppN thm.proof args)

elab "cassels_structural_exact " supplied:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let source ← Term.elabTerm supplied none
    Term.synthesizeSyntheticMVarsNoPostponing
    let source ← instantiateMVars source
    let sourceType ← inferType source
    let target ← goal.getType
    let (heq, state) ← (structuralHEq sourceType target 96 #[]).run {}
    let eq ← mkEqOfHEq heq
    let finalProof := mkAppN (mkConst ``Eq.mp [Level.zero])
      #[sourceType, target, eq, source]
    logInfo m!"Structural081 certificate: proof leaves={state.proofLeaves}, abstract congruence steps={state.congrSteps}, binder steps={state.binderSteps}, unused traversal budget={state.remaining}."
    goal.assign finalProof
    replaceMainGoal []

end CasselsStructuralCertificate081
end

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite IdealSheafDataModule
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] actualOriginalNativeIdealTwistConstructedChartData
attribute [local irreducible] actualOriginalQuarticCotangentChartChoice

set_option backward.isDefEq.respectTransparency true in
lemma actualOriginalIdealTwistLocalBasisRefinement
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let f := chartι I C.index
    ∀ (U : (hypersurface p hp).Opens) (m : J.val.obj (op U)),
      (actualOriginalNativeIdealTwistChartIso p hp P hP).hom.val.app (op (f ⁻¹ᵁ U))
        (((Scheme.Modules.restrictAdjunction f).unit.app (schemeModuleTensor J T)).val.app
          (op U) (actualModuleLocalTensorSection J T U m
            (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))) =
      (actualOriginalNativeUntwistedIdealChartIso p hp P hP).hom.val.app (op (f ⁻¹ᵁ U))
        (((Scheme.Modules.restrictAdjunction f).unit.app J).val.app (op U) m) := by
  cassels_structural_exact (actualOriginalPublicIdealLocalBasisLawProof p hp P hP)

end PfaffianDescent
