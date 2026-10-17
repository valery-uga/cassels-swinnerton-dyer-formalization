import PfaffianDescent.SchemeModuleClosedPointCanonicalOpenFrame
import PfaffianDescent.SchemeModuleCanonicalChartFunctionField
import PfaffianDescent.SchemeModuleRankOneDualKernelIso

/-! Canonical function-field maps for the SAME point ideal and its actual
O-linear dual. Their frames are the original ideal inclusion on the actual
punctured open and evaluation on its inverse. The generic helper exposes
ordinary nongeneric/rank-one hypotheses; the primitive caller proves both.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open IdealSheafDataModule
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual complement of the original closed point. -/
def schemeClosedPointComplementOpen (P : closedPoints X) : X.Opens :=
  ⟨({P.1} : Set X)ᶜ, P.2.isOpen_compl⟩

/-- The SAME closed point is absent from its punctured open. -/
theorem schemeClosedPoint_not_mem_complement (P : closedPoints X) :
    P.1 ∉ schemeClosedPointComplementOpen P := by
  change P.1 ∉ ({P.1} : Set X)ᶜ
  simp

/-- The generic point belongs to this genuine punctured open whenever
P is nongeneric. No chosen rational chart is an input. -/
theorem schemeClosedPoint_generic_mem_complement
    (P : closedPoints X) (hP : P.1 ≠ genericPoint X) :
    genericPoint X ∈ schemeClosedPointComplementOpen P := by
  change genericPoint X ∉ ({P.1} : Set X)
  simpa only [Set.mem_singleton_iff] using hP.symm

/-- The original ideal inclusion determines the actual global field map;
its section restriction and original-pi scalar structure are unchanged. -/
def schemeModuleClosedPointIdealToFunctionFieldLinearMap
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    SchemeModuleOpenSectionsOver pi (closedImmersionModule i) ⊤ →ₗ[K]
      SchemeFunctionFieldOver pi := by
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let U := schemeClosedPointComplementOpen P
  exact schemeModuleTopSectionsToFunctionFieldLinearMap pi (closedImmersionModule i) U
    (schemeClosedPoint_generic_mem_complement P hP)
    (schemeModuleClosedPointIdealOverCanonicalIso P U (schemeClosedPoint_not_mem_complement P))

/-- The original dual's global field map uses its actual evaluation on
the inverse inclusion frame, with independently original-pi field scalars. -/
def schemeModuleClosedPointDualToFunctionFieldLinearMap
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    SchemeModuleOpenSectionsOver pi (SchemeModuleInternalHom.dual (closedImmersionModule i)) ⊤ →ₗ[K]
      SchemeFunctionFieldOver pi := by
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let U := schemeClosedPointComplementOpen P
  exact schemeModuleTopSectionsToFunctionFieldLinearMap pi
    (SchemeModuleInternalHom.dual (closedImmersionModule i)) U
    (schemeClosedPoint_generic_mem_complement P hP)
    (schemeModuleClosedPointDualOverCanonicalIso P U (schemeClosedPoint_not_mem_complement P))

/-- Genuine ideal-section injectivity from ordinary rank-one geometry;
no field-map or dense-restriction injectivity hypothesis is supplied. -/
theorem schemeModuleClosedPointIdealToFunctionFieldLinearMap_injective
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X)
    (hM : let i := X.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      schemeModuleLocallyRankOne (closedImmersionModule i)) :
    Function.Injective (schemeModuleClosedPointIdealToFunctionFieldLinearMap pi P hP) := by
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let U := schemeClosedPointComplementOpen P
  exact schemeModuleTopSectionsToFunctionFieldLinearMap_injective pi (closedImmersionModule i)
    hM U (schemeClosedPoint_generic_mem_complement P hP)
    (schemeModuleClosedPointIdealOverCanonicalIso P U (schemeClosedPoint_not_mem_complement P))

/-- Genuine actual-dual injectivity; the dual's rank-one charts are
internally derived from M's charts by the actual dual evaluation. -/
theorem schemeModuleClosedPointDualToFunctionFieldLinearMap_injective
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X)
    (hM : let i := X.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      schemeModuleLocallyRankOne (closedImmersionModule i)) :
    Function.Injective (schemeModuleClosedPointDualToFunctionFieldLinearMap pi P hP) := by
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let U := schemeClosedPointComplementOpen P
  exact schemeModuleTopSectionsToFunctionFieldLinearMap_injective pi
    (SchemeModuleInternalHom.dual (closedImmersionModule i))
    (schemeModuleLocallyRankOne_dual (closedImmersionModule i) hM) U
    (schemeClosedPoint_generic_mem_complement P hP)
    (schemeModuleClosedPointDualOverCanonicalIso P U (schemeClosedPoint_not_mem_complement P))

/-- Literal inclusion/generic-germ formula. The canonical ideal map is
not an unrelated choice of rational frame: it is the original inclusion
followed by the original generic germ on global functions. -/
theorem schemeModuleClosedPointIdealToFunctionFieldLinearMap_apply
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleOpenSectionsOver pi (closedImmersionModule i) ⊤,
      schemeModuleClosedPointIdealToFunctionFieldLinearMap pi P hP s =
        X.presheaf.germ ⊤ (genericPoint X) trivial
          ((closedImmersionModuleToUnit i).val.app (op ⊤) s) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  let j := closedImmersionModuleToUnit i
  let U := schemeClosedPointComplementOpen P
  have hgU : genericPoint X ∈ U := schemeClosedPoint_generic_mem_complement P hP
  letI : Nonempty U := ⟨⟨genericPoint X, hgU⟩⟩
  intro s
  change X.germToFunctionField U
      (j.val.app (op U) (M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op s)) =
    X.presheaf.germ ⊤ (genericPoint X) trivial (j.val.app (op ⊤) s)
  exact (congrArg (X.germToFunctionField U)
    (PresheafOfModules.naturality_apply j.val (homOfLE (show U ≤ ⊤ from le_top)).op s)).trans
      (X.presheaf.germ_res_apply (homOfLE (show U ≤ ⊤ from le_top))
        (genericPoint X) hgU (j.val.app (op ⊤) s))

end PfaffianDescent
