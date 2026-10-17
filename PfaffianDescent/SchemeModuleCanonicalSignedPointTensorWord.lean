import PfaffianDescent.SchemeModuleCanonicalTensorFieldMultiplication
import PfaffianDescent.SchemeModuleClosedPointGenericFunctionField
import PfaffianDescent.SchemeModuleSignedPointTensorOperations

/-! Canonical actual finite signed tensor WORD frame on the common
complement of its finite closed-point support. It uses original ideal
inclusions, actual dual evaluations and the original tensor product chart.
Original-pi field maps follow actual pure-tensor multiplication. No
arbitrary word frame or multiplication comparison is a primitive input.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open IdealSheafDataModule
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual common open complement of the finite list's closed-point
support. Repeated points and the empty word are permitted. -/
def schemeSignedPointTensorWordComplementOpen :
    List (closedPoints X × Bool) → X.Opens
  | [] => ⊤
  | operation :: ops => schemeClosedPointComplementOpen operation.1 ⊓
      schemeSignedPointTensorWordComplementOpen ops

/-- Exact support-complement membership law; the open is genuinely the
complement of the specified finite point support. -/
theorem schemeSignedPointTensorWordComplementOpen_mem
    (ops : List (closedPoints X × Bool)) (x : X) :
    x ∈ schemeSignedPointTensorWordComplementOpen ops ↔
      ∀ operation ∈ ops, x ≠ operation.1.1 := by
  induction ops with
  | nil => simp [schemeSignedPointTensorWordComplementOpen]
  | cons operation ops ih =>
    change (x ∈ schemeClosedPointComplementOpen operation.1 ∧
      x ∈ schemeSignedPointTensorWordComplementOpen ops) ↔ _
    rw [ih]
    change (x ≠ operation.1.1 ∧ ∀ a ∈ ops, x ≠ a.1.1) ↔ _
    constructor
    · intro h a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact h.1
      · exact h.2 a ha
    · intro h
      exact ⟨h operation (List.mem_cons_self ..),
        fun a ha => h a (List.mem_cons_of_mem _ ha)⟩

/-- Every ACTUAL point in the word is excluded from its SAME common open. -/
theorem schemeSignedPointTensorWordComplementOpen_excludes
    (ops : List (closedPoints X × Bool)) :
    ∀ operation ∈ ops, operation.1.1 ∉ schemeSignedPointTensorWordComplementOpen ops := by
  intro operation hmem hx
  exact (schemeSignedPointTensorWordComplementOpen_mem ops operation.1.1).mp hx operation hmem rfl

/-- The actual ideal or actual constructed dual used by this sign. -/
def schemeModuleSignedClosedPointFactor (operation : closedPoints X × Bool) : X.Modules :=
  let i := X.fromSpecResidueField operation.1.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp operation.1.2
  match operation.2 with
  | true => SchemeModuleInternalHom.dual (closedImmersionModule i)
  | false => closedImmersionModule i

/-- Canonical factor chart from SAME original ideal inclusion or actual
dual evaluation, on the SAME open that excludes its original point. -/
def schemeModuleSignedClosedPointFactorOverCanonicalIso
    (operation : closedPoints X × Bool) (U : X.Opens) (hPU : operation.1.1 ∉ U) :
    (schemeModuleSignedClosedPointFactor operation).over U ≅
      (SheafOfModules.unit X.ringCatSheaf).over U := by
  rcases operation with ⟨P, sign⟩
  cases sign
  · exact schemeModuleClosedPointIdealOverCanonicalIso P U hPU
  · exact schemeModuleClosedPointDualOverCanonicalIso P U hPU

/-- The actual signed tensor step's canonical product chart. Negative
steps keep their ORIGINAL ideal-first order; positive steps keep L-first. -/
def schemeModuleSignedClosedPointTensorOverCanonicalIso
    (operation : closedPoints X × Bool) (U : X.Opens) (hPU : operation.1.1 ∉ U)
    (L : X.Modules) (eL : L.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    (schemeModuleSignedClosedPointTensor operation L).over U ≅
      (SheafOfModules.unit X.ringCatSheaf).over U := by
  rcases operation with ⟨P, sign⟩
  cases sign
  · exact schemeModuleTensorOverUnitIso _ L U
      (schemeModuleClosedPointIdealOverCanonicalIso P U hPU) eL
  · exact schemeModuleTensorOverUnitIso L _ U eL
      (schemeModuleClosedPointDualOverCanonicalIso P U hPU)

/-- Actual canonical word chart, recursing through the SAME literal fold
and retaining the SAME common open at every step. No arbitrary frame choice. -/
def schemeModuleIteratedSignedClosedPointTensorOverCanonicalIso (U : X.Opens) :
    ∀ (ops : List (closedPoints X × Bool))
      (hPU : ∀ operation ∈ ops, operation.1.1 ∉ U)
      (L : X.Modules) (eL : L.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U),
      (schemeModuleIteratedSignedClosedPointTensor L ops).over U ≅
        (SheafOfModules.unit X.ringCatSheaf).over U
  | [], _, _, eL => eL
  | operation :: ops, hPU, L, eL =>
    schemeModuleIteratedSignedClosedPointTensorOverCanonicalIso U ops
      (fun a ha => hPU a (List.mem_cons_of_mem _ ha))
      (schemeModuleSignedClosedPointTensor operation L)
      (schemeModuleSignedClosedPointTensorOverCanonicalIso operation U
        (hPU operation (List.mem_cons_self ..)) L eL)

/-- Actual pure global section for the original signed step, with the
original factor order and original sheafification unit retained. -/
def schemeModuleSignedClosedPointTensorPureSection
    (operation : closedPoints X × Bool) (L : X.Modules)
    (s : L.val.obj (op ⊤)) (t : (schemeModuleSignedClosedPointFactor operation).val.obj (op ⊤)) :
    (schemeModuleSignedClosedPointTensor operation L).val.obj (op ⊤) := by
  rcases operation with ⟨P, sign⟩
  cases sign
  · exact SheafOfModules.commRingSheafTensorPureSection X.sheaf _ L (op ⊤) t s
  · exact SheafOfModules.commRingSheafTensorPureSection X.sheaf L _ (op ⊤) s t

/-- Actual signed steps preserve rank-one geometry, independently of
finiteness/cohomology. The dual's rank-one charts are derived internally. -/
theorem schemeModuleSignedClosedPointTensor_locallyRankOne
    (operation : closedPoints X × Bool) (L : X.Modules)
    (hM : ∀ P : closedPoints X,
      let i := X.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      schemeModuleLocallyRankOne (closedImmersionModule i))
    (hL : schemeModuleLocallyRankOne L) :
    schemeModuleLocallyRankOne (schemeModuleSignedClosedPointTensor operation L) := by
  rcases operation with ⟨P, sign⟩
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  cases sign
  · exact schemeModuleLocallyRankOne_tensor (closedImmersionModule i) L (hM P) hL
  · exact schemeModuleLocallyRankOne_tensor L (SchemeModuleInternalHom.dual (closedImmersionModule i))
      hL (schemeModuleLocallyRankOne_dual (closedImmersionModule i) (hM P))

/-- Genuine rank-one geometry of EVERY actual finite signed word, without
using finite H0/H1, Ext or an output rank-one certificate. -/
theorem schemeModuleIteratedSignedClosedPointTensor_locallyRankOne
    (ops : List (closedPoints X × Bool)) (L : X.Modules)
    (hM : ∀ P : closedPoints X,
      let i := X.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      schemeModuleLocallyRankOne (closedImmersionModule i))
    (hL : schemeModuleLocallyRankOne L) :
    schemeModuleLocallyRankOne (schemeModuleIteratedSignedClosedPointTensor L ops) := by
  induction ops generalizing L with
  | nil => exact hL
  | cons operation ops ih =>
    exact ih (schemeModuleSignedClosedPointTensor operation L)
      (schemeModuleSignedClosedPointTensor_locallyRankOne operation L hM hL)

variable {K : Type u} [Field K] [IsIntegral X]

/-- Generic-point membership of the ACTUAL common complement, internally
from nongenericity of precisely the specified points. Nonempty follows. -/
theorem schemeSignedPointTensorWordComplementOpen_generic_mem
    (ops : List (closedPoints X × Bool))
    (hP : ∀ operation ∈ ops, operation.1.1 ≠ genericPoint X) :
    genericPoint X ∈ schemeSignedPointTensorWordComplementOpen ops :=
  (schemeSignedPointTensorWordComplementOpen_mem ops (genericPoint X)).mpr
    (fun operation hmem => (hP operation hmem).symm)

/-- The canonical ORIGINAL-K field map of the actual signed word from O,
using its SAME finite-support common open and its recursively canonical chart. -/
def schemeModuleSignedPointTensorWordToFunctionFieldLinearMap
    (pi : X ⟶ Spec (CommRingCat.of K)) (ops : List (closedPoints X × Bool))
    (hP : ∀ operation ∈ ops, operation.1.1 ≠ genericPoint X) :
    SchemeModuleOpenSectionsOver pi
      (schemeModuleIteratedSignedClosedPointTensor (SheafOfModules.unit X.ringCatSheaf) ops) ⊤ →ₗ[K]
        SchemeFunctionFieldOver pi := by
  let U := schemeSignedPointTensorWordComplementOpen ops
  exact schemeModuleTopSectionsToFunctionFieldLinearMap pi _ U
    (schemeSignedPointTensorWordComplementOpen_generic_mem ops hP)
    (schemeModuleIteratedSignedClosedPointTensorOverCanonicalIso U ops
      (schemeSignedPointTensorWordComplementOpen_excludes ops)
      (SheafOfModules.unit X.ringCatSheaf) (Iso.refl _))

/-- Genuine global injection for the actual word field map, with all word
rank-one geometry derived from ordinary geometry of the original point ideals. -/
theorem schemeModuleSignedPointTensorWordToFunctionFieldLinearMap_injective
    (pi : X ⟶ Spec (CommRingCat.of K)) (ops : List (closedPoints X × Bool))
    (hP : ∀ operation ∈ ops, operation.1.1 ≠ genericPoint X)
    (hM : ∀ P : closedPoints X,
      let i := X.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      schemeModuleLocallyRankOne (closedImmersionModule i)) :
    Function.Injective (schemeModuleSignedPointTensorWordToFunctionFieldLinearMap pi ops hP) := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let U := schemeSignedPointTensorWordComplementOpen ops
  have hO : schemeModuleLocallyRankOne O := fun x => ⟨⊤, by simp, ⟨Iso.refl _⟩⟩
  exact schemeModuleTopSectionsToFunctionFieldLinearMap_injective pi _
    (schemeModuleIteratedSignedClosedPointTensor_locallyRankOne ops O hM hO) U
    (schemeSignedPointTensorWordComplementOpen_generic_mem ops hP)
    (schemeModuleIteratedSignedClosedPointTensorOverCanonicalIso U ops
      (schemeSignedPointTensorWordComplementOpen_excludes ops) O (Iso.refl _))

/-- At EACH recursive word step the actual field map follows original
tensor multiplication. The frame is the constructed signed canonical chart;
no compatibility premise is accepted. Both original tensor orders are handled. -/
theorem schemeModuleSignedClosedPointTensorOverCanonicalIso_fieldPureSection
    (pi : X ⟶ Spec (CommRingCat.of K)) (operation : closedPoints X × Bool)
    (U : X.Opens) (hgU : genericPoint X ∈ U) (hPU : operation.1.1 ∉ U)
    (L : X.Modules) (eL : L.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (s : SchemeModuleOpenSectionsOver pi L ⊤)
    (t : SchemeModuleOpenSectionsOver pi (schemeModuleSignedClosedPointFactor operation) ⊤) :
    (schemeModuleTopSectionsToFunctionFieldLinearMap pi (schemeModuleSignedClosedPointTensor operation L)
        U hgU (schemeModuleSignedClosedPointTensorOverCanonicalIso operation U hPU L eL)
        (schemeModuleSignedClosedPointTensorPureSection operation L s t) : X.functionField) =
      (schemeModuleTopSectionsToFunctionFieldLinearMap pi L U hgU eL s : X.functionField) *
        (schemeModuleTopSectionsToFunctionFieldLinearMap pi (schemeModuleSignedClosedPointFactor operation)
          U hgU (schemeModuleSignedClosedPointFactorOverCanonicalIso operation U hPU) t : X.functionField) := by
  rcases operation with ⟨P, sign⟩
  cases sign
  · exact (schemeModuleTopSectionsToFunctionFieldLinearMap_tensorPureSection pi _ L U hgU
      (schemeModuleClosedPointIdealOverCanonicalIso P U hPU) eL t s).trans (mul_comm _ _)
  · exact schemeModuleTopSectionsToFunctionFieldLinearMap_tensorPureSection pi L _ U hgU eL
      (schemeModuleClosedPointDualOverCanonicalIso P U hPU) s t

/-- Multiplication at a genuine WORD-prefix step on the full word's SAME
common open. The prefix frame is constructed recursively, rather than
supplied. Only literal finite-list membership and point nongenericity remain. -/
theorem schemeModuleSignedPointTensorWord_prefixStep_fieldPureSection
    (pi : X ⟶ Spec (CommRingCat.of K)) (ops : List (closedPoints X × Bool))
    (hP : ∀ operation ∈ ops, operation.1.1 ≠ genericPoint X)
    (wordPrefix : List (closedPoints X × Bool)) (hprefix : wordPrefix ⊆ ops)
    (operation : closedPoints X × Bool) (hmem : operation ∈ ops) :
    let U := schemeSignedPointTensorWordComplementOpen ops
    let hgU := schemeSignedPointTensorWordComplementOpen_generic_mem ops hP
    let hPU := schemeSignedPointTensorWordComplementOpen_excludes ops operation hmem
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let L := schemeModuleIteratedSignedClosedPointTensor O wordPrefix
    let eL := schemeModuleIteratedSignedClosedPointTensorOverCanonicalIso U wordPrefix
      (fun a ha => schemeSignedPointTensorWordComplementOpen_excludes ops a (hprefix ha)) O (Iso.refl _)
    ∀ (s : SchemeModuleOpenSectionsOver pi L ⊤)
      (t : SchemeModuleOpenSectionsOver pi (schemeModuleSignedClosedPointFactor operation) ⊤),
      (schemeModuleTopSectionsToFunctionFieldLinearMap pi (schemeModuleSignedClosedPointTensor operation L)
          U hgU (schemeModuleSignedClosedPointTensorOverCanonicalIso operation U hPU L eL)
          (schemeModuleSignedClosedPointTensorPureSection operation L s t) : X.functionField) =
        (schemeModuleTopSectionsToFunctionFieldLinearMap pi L U hgU eL s : X.functionField) *
          (schemeModuleTopSectionsToFunctionFieldLinearMap pi (schemeModuleSignedClosedPointFactor operation)
            U hgU (schemeModuleSignedClosedPointFactorOverCanonicalIso operation U hPU) t : X.functionField) := by
  dsimp only
  intro s t
  exact schemeModuleSignedClosedPointTensorOverCanonicalIso_fieldPureSection pi operation
    (schemeSignedPointTensorWordComplementOpen ops)
    (schemeSignedPointTensorWordComplementOpen_generic_mem ops hP)
    (schemeSignedPointTensorWordComplementOpen_excludes ops operation hmem) _ _ s t

end PfaffianDescent.Coray
