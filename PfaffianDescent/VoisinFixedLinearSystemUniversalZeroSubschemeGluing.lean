import PfaffianDescent.VoisinFixedLinearSystemUniversalZeroSubschemeDescent
import PfaffianDescent.VoisinFixedLinearSystemUniversalChart
import PfaffianDescent.VoisinFixedLinearSystemFamily
import PfaffianDescent.ClosedImmersionPointLift
import AllCharacteristics.OverlapCompositionGluing
import AllCharacteristics.SchemeGlueDataDescent
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing the projective universal zero subschemes

The pairwise transitions for the local universal zero loci are completed to
triple-overlap crossing maps and categorical scheme gluing data.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective

universe u

noncomputable section

namespace SchemeModuleFiniteFreeAffineCover

/-- The map from a local universal zero subscheme to the ambient universal
product. -/
noncomputable def projectiveSectionLocalZeroToAmbient
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroSubscheme base M ij ⟶
      pullback base
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M) :=
  (C.projectiveSectionLocalZeroIdeal base M ij).subschemeι ≫
    (C.projectiveSectionOpenCover base M).f ij

/-- The two presentations of a local zero overlap induce the same map to the
ambient universal product. -/
theorem projectiveSectionLocalZeroOverlapRightMap_comp_toAmbient
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroOverlapRightMap base M ij kl ≫
        C.projectiveSectionLocalZeroToAmbient base M kl =
      C.projectiveSectionLocalZeroOverlapι base M ij kl ≫
        C.projectiveSectionLocalZeroToAmbient base M ij := by
  unfold projectiveSectionLocalZeroToAmbient
  exact C.projectiveSectionLocalZeroOverlapRightMap_comp_ambient_eq_left
    base M ij kl

/-- The map from the intersection of the `ij` and `ik` zero overlaps to the
local zero subscheme on chart `j`. -/
noncomputable def projectiveSectionLocalZeroTripleToJ
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij jk kl : (C.projectiveSectionOpenCover base M).I₀) :
    pullback
        (C.projectiveSectionLocalZeroOverlapι base M ij jk)
        (C.projectiveSectionLocalZeroOverlapι base M ij kl) ⟶
      C.projectiveSectionLocalZeroSubscheme base M jk :=
  pullback.fst
      (C.projectiveSectionLocalZeroOverlapι base M ij jk)
      (C.projectiveSectionLocalZeroOverlapι base M ij kl) ≫
    C.projectiveSectionLocalZeroOverlapRightMap base M ij jk

/-- The analogous map to the local zero subscheme on chart `k`. -/
noncomputable def projectiveSectionLocalZeroTripleToK
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij jk kl : (C.projectiveSectionOpenCover base M).I₀) :
    pullback
        (C.projectiveSectionLocalZeroOverlapι base M ij jk)
        (C.projectiveSectionLocalZeroOverlapι base M ij kl) ⟶
      C.projectiveSectionLocalZeroSubscheme base M kl :=
  pullback.snd
      (C.projectiveSectionLocalZeroOverlapι base M ij jk)
      (C.projectiveSectionLocalZeroOverlapι base M ij kl) ≫
    C.projectiveSectionLocalZeroOverlapRightMap base M ij kl

/-- The first triple-overlap map, viewed in the ambient product chart. -/
noncomputable def projectiveSectionLocalZeroTripleToJChart
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij jk kl : (C.projectiveSectionOpenCover base M).I₀) :
    pullback
        (C.projectiveSectionLocalZeroOverlapι base M ij jk)
        (C.projectiveSectionLocalZeroOverlapι base M ij kl) ⟶
      (C.projectiveSectionOpenCover base M).X jk :=
  C.projectiveSectionLocalZeroTripleToJ base M ij jk kl ≫
    (C.projectiveSectionLocalZeroIdeal base M jk).subschemeι

/-- The second triple-overlap map, viewed in the ambient product chart. -/
noncomputable def projectiveSectionLocalZeroTripleToKChart
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij jk kl : (C.projectiveSectionOpenCover base M).I₀) :
    pullback
        (C.projectiveSectionLocalZeroOverlapι base M ij jk)
        (C.projectiveSectionLocalZeroOverlapι base M ij kl) ⟶
      (C.projectiveSectionOpenCover base M).X kl :=
  C.projectiveSectionLocalZeroTripleToK base M ij jk kl ≫
    (C.projectiveSectionLocalZeroIdeal base M kl).subschemeι

/-- The map through the first pairwise overlap has the ambient presentation
coming from its left chart. -/
theorem projectiveSectionLocalZeroTripleToJ_comp_ambient
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij jk kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroTripleToJChart base M ij jk kl ≫
        (C.projectiveSectionOpenCover base M).f jk =
      pullback.fst
          (C.projectiveSectionLocalZeroOverlapι base M ij jk)
          (C.projectiveSectionLocalZeroOverlapι base M ij kl) ≫
        C.projectiveSectionLocalZeroOverlapι base M ij jk ≫
        (C.projectiveSectionLocalZeroIdeal base M ij).subschemeι ≫
        (C.projectiveSectionOpenCover base M).f ij := by
  unfold projectiveSectionLocalZeroTripleToJChart
    projectiveSectionLocalZeroTripleToJ
  have h := congrArg
    (fun z => pullback.fst
      (C.projectiveSectionLocalZeroOverlapι base M ij jk)
      (C.projectiveSectionLocalZeroOverlapι base M ij kl) ≫ z)
    (C.projectiveSectionLocalZeroOverlapRightMap_comp_ambient_eq_left
      base M ij jk)
  simpa only [Category.assoc] using h

/-- The map through the second pairwise overlap has the ambient presentation
coming from its left chart. -/
theorem projectiveSectionLocalZeroTripleToK_comp_ambient
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij jk kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroTripleToKChart base M ij jk kl ≫
        (C.projectiveSectionOpenCover base M).f kl =
      pullback.snd
          (C.projectiveSectionLocalZeroOverlapι base M ij jk)
          (C.projectiveSectionLocalZeroOverlapι base M ij kl) ≫
        C.projectiveSectionLocalZeroOverlapι base M ij kl ≫
        (C.projectiveSectionLocalZeroIdeal base M ij).subschemeι ≫
        (C.projectiveSectionOpenCover base M).f ij := by
  unfold projectiveSectionLocalZeroTripleToKChart
    projectiveSectionLocalZeroTripleToK
  have h := congrArg
    (fun z => pullback.snd
      (C.projectiveSectionLocalZeroOverlapι base M ij jk)
      (C.projectiveSectionLocalZeroOverlapι base M ij kl) ≫ z)
    (C.projectiveSectionLocalZeroOverlapRightMap_comp_ambient_eq_left
      base M ij kl)
  simpa only [Category.assoc] using h

/-- The two maps from a triple zero overlap agree in the ambient universal
product. -/
theorem projectiveSectionLocalZeroTriple_ambient_condition
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij jk kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroTripleToJChart base M ij jk kl ≫
        (C.projectiveSectionOpenCover base M).f jk =
      C.projectiveSectionLocalZeroTripleToKChart base M ij jk kl ≫
        (C.projectiveSectionOpenCover base M).f kl := by
  rw [C.projectiveSectionLocalZeroTripleToJ_comp_ambient base M ij jk kl,
    C.projectiveSectionLocalZeroTripleToK_comp_ambient base M ij jk kl]
  let p := pullback.fst
    (C.projectiveSectionLocalZeroOverlapι base M ij jk)
    (C.projectiveSectionLocalZeroOverlapι base M ij kl)
  let q := pullback.snd
    (C.projectiveSectionLocalZeroOverlapι base M ij jk)
    (C.projectiveSectionLocalZeroOverlapι base M ij kl)
  have hpq := congrArg
    (fun z => z ≫ (C.projectiveSectionLocalZeroIdeal base M ij).subschemeι ≫
      (C.projectiveSectionOpenCover base M).f ij)
    (pullback.condition
      (f := C.projectiveSectionLocalZeroOverlapι base M ij jk)
      (g := C.projectiveSectionLocalZeroOverlapι base M ij kl))
  simpa only [Category.assoc] using hpq

/-- The induced map from the triple zero overlap to the ambient `j,k` chart
overlap. -/
noncomputable def projectiveSectionLocalZeroTripleToAmbientOverlap
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij jk kl : (C.projectiveSectionOpenCover base M).I₀) :
    pullback
        (C.projectiveSectionLocalZeroOverlapι base M ij jk)
        (C.projectiveSectionLocalZeroOverlapι base M ij kl) ⟶
      C.projectiveSectionOpenCoverOverlap base M jk kl :=
  pullback.lift
    (C.projectiveSectionLocalZeroTripleToJChart base M ij jk kl)
    (C.projectiveSectionLocalZeroTripleToKChart base M ij jk kl)
    (C.projectiveSectionLocalZeroTriple_ambient_condition base M ij jk kl)

/-- The triple-overlap crossing to the `j,k` zero overlap, obtained from the
pullback square defining restriction of the `j`-th zero locus. -/
noncomputable def projectiveSectionLocalZeroTripleCross
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij jk kl : (C.projectiveSectionOpenCover base M).I₀) :
    pullback
        (C.projectiveSectionLocalZeroOverlapι base M ij jk)
        (C.projectiveSectionLocalZeroOverlapι base M ij kl) ⟶
      C.projectiveSectionLocalZeroOverlap base M jk kl :=
  let hPB := C.isPullback_projectiveSectionLocalZeroOverlap base M jk kl
  hPB.lift
    (C.projectiveSectionLocalZeroTripleToAmbientOverlap base M ij jk kl)
    (C.projectiveSectionLocalZeroTripleToJ base M ij jk kl)
    (pullback.lift_fst _ _ _)

/-- The triple crossing has the required left projection. -/
theorem projectiveSectionLocalZeroTripleCross_fac
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij jk kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroTripleCross base M ij jk kl ≫
        C.projectiveSectionLocalZeroOverlapι base M jk kl =
      pullback.fst
        (C.projectiveSectionLocalZeroOverlapι base M ij jk)
        (C.projectiveSectionLocalZeroOverlapι base M ij kl) ≫
          C.projectiveSectionLocalZeroOverlapRightMap base M ij jk := by
  unfold projectiveSectionLocalZeroTripleCross
    projectiveSectionLocalZeroTripleToJ
  exact (C.isPullback_projectiveSectionLocalZeroOverlap base M jk kl).lift_snd _ _ _

/-- After composing with the ambient map, the right projection of the
crossing is the first pairwise right projection. -/
theorem projectiveSectionLocalZeroTripleCross_right_toAmbient_eq_fst
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij jk kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroTripleCross base M ij jk kl ≫
        C.projectiveSectionLocalZeroOverlapRightMap base M jk kl ≫
        C.projectiveSectionLocalZeroToAmbient base M kl =
      pullback.fst
          (C.projectiveSectionLocalZeroOverlapι base M ij jk)
          (C.projectiveSectionLocalZeroOverlapι base M ij kl) ≫
        C.projectiveSectionLocalZeroOverlapRightMap base M ij jk ≫
        C.projectiveSectionLocalZeroToAmbient base M jk := by
  calc
    C.projectiveSectionLocalZeroTripleCross base M ij jk kl ≫
        C.projectiveSectionLocalZeroOverlapRightMap base M jk kl ≫
        C.projectiveSectionLocalZeroToAmbient base M kl =
      C.projectiveSectionLocalZeroTripleCross base M ij jk kl ≫
        C.projectiveSectionLocalZeroOverlapι base M jk kl ≫
        C.projectiveSectionLocalZeroToAmbient base M jk := by
          rw [C.projectiveSectionLocalZeroOverlapRightMap_comp_toAmbient
              base M jk kl]
    _ = pullback.fst
          (C.projectiveSectionLocalZeroOverlapι base M ij jk)
          (C.projectiveSectionLocalZeroOverlapι base M ij kl) ≫
        C.projectiveSectionLocalZeroOverlapRightMap base M ij jk ≫
        C.projectiveSectionLocalZeroToAmbient base M jk := by
          simpa only [Category.assoc] using congrArg
            (fun z => z ≫ C.projectiveSectionLocalZeroToAmbient base M jk)
            (C.projectiveSectionLocalZeroTripleCross_fac base M ij jk kl)

/-- The two pairwise right projections from a triple overlap agree after
composition with the ambient universal product. -/
theorem projectiveSectionLocalZeroTriple_fst_right_toAmbient_eq_snd
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij jk kl : (C.projectiveSectionOpenCover base M).I₀) :
    pullback.fst
          (C.projectiveSectionLocalZeroOverlapι base M ij jk)
          (C.projectiveSectionLocalZeroOverlapι base M ij kl) ≫
        C.projectiveSectionLocalZeroOverlapRightMap base M ij jk ≫
        C.projectiveSectionLocalZeroToAmbient base M jk =
      pullback.snd
          (C.projectiveSectionLocalZeroOverlapι base M ij jk)
          (C.projectiveSectionLocalZeroOverlapι base M ij kl) ≫
        C.projectiveSectionLocalZeroOverlapRightMap base M ij kl ≫
        C.projectiveSectionLocalZeroToAmbient base M kl := by
  calc
    pullback.fst
          (C.projectiveSectionLocalZeroOverlapι base M ij jk)
          (C.projectiveSectionLocalZeroOverlapι base M ij kl) ≫
        C.projectiveSectionLocalZeroOverlapRightMap base M ij jk ≫
        C.projectiveSectionLocalZeroToAmbient base M jk =
      pullback.fst
          (C.projectiveSectionLocalZeroOverlapι base M ij jk)
          (C.projectiveSectionLocalZeroOverlapι base M ij kl) ≫
        C.projectiveSectionLocalZeroOverlapι base M ij jk ≫
        C.projectiveSectionLocalZeroToAmbient base M ij := by
          rw [C.projectiveSectionLocalZeroOverlapRightMap_comp_toAmbient
              base M ij jk]
    _ = pullback.snd
          (C.projectiveSectionLocalZeroOverlapι base M ij jk)
          (C.projectiveSectionLocalZeroOverlapι base M ij kl) ≫
        C.projectiveSectionLocalZeroOverlapι base M ij kl ≫
        C.projectiveSectionLocalZeroToAmbient base M ij := by
          simpa only [Category.assoc] using congrArg
            (fun z => z ≫ C.projectiveSectionLocalZeroToAmbient base M ij)
            (pullback.condition
              (f := C.projectiveSectionLocalZeroOverlapι base M ij jk)
              (g := C.projectiveSectionLocalZeroOverlapι base M ij kl))
    _ = pullback.snd
          (C.projectiveSectionLocalZeroOverlapι base M ij jk)
          (C.projectiveSectionLocalZeroOverlapι base M ij kl) ≫
        C.projectiveSectionLocalZeroOverlapRightMap base M ij kl ≫
        C.projectiveSectionLocalZeroToAmbient base M kl := by
          rw [C.projectiveSectionLocalZeroOverlapRightMap_comp_toAmbient
              base M ij kl]

/-- The triple crossing has the required right projection. -/
theorem projectiveSectionLocalZeroTripleCross_right
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij jk kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroTripleCross base M ij jk kl ≫
        C.projectiveSectionLocalZeroOverlapRightMap base M jk kl =
      pullback.snd
        (C.projectiveSectionLocalZeroOverlapι base M ij jk)
        (C.projectiveSectionLocalZeroOverlapι base M ij kl) ≫
          C.projectiveSectionLocalZeroOverlapRightMap base M ij kl := by
  letI : Mono (C.projectiveSectionLocalZeroToAmbient base M kl) := by
    unfold projectiveSectionLocalZeroToAmbient
    infer_instance
  apply (cancel_mono
    (C.projectiveSectionLocalZeroToAmbient base M kl)).mp
  simpa only [Category.assoc] using
    (C.projectiveSectionLocalZeroTripleCross_right_toAmbient_eq_fst
      base M ij jk kl).trans
    (C.projectiveSectionLocalZeroTriple_fst_right_toAmbient_eq_snd
      base M ij jk kl)

/-- Restriction of a local zero locus to its self-overlap is an
isomorphism. -/
theorem isIso_projectiveSectionLocalZeroOverlapι_self
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    IsIso (C.projectiveSectionLocalZeroOverlapι base M ij ij) := by
  let g := (C.projectiveSectionOpenCover base M).f ij
  let p := pullback.fst g g
  let J := C.projectiveSectionLocalZeroIdeal base M ij
  change IsIso ((J.comapIso p).hom ≫ pullback.snd p J.subschemeι)
  letI : IsOpenImmersion g :=
    (C.projectiveSectionOpenCover base M).map_prop ij
  letI : IsIso p := by infer_instance
  infer_instance

/-- The diagonal overlap isomorphism is available to the categorical gluing
constructor. -/
instance isIso_projectiveSectionLocalZeroOverlapι_self_instance
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    IsIso (C.projectiveSectionLocalZeroOverlapι base M ij ij) :=
  C.isIso_projectiveSectionLocalZeroOverlapι_self base M ij

/-- The local universal zero loci and their proved pairwise and triple
transition maps form categorical gluing data. -/
noncomputable def projectiveSectionLocalZeroCategoryGlueData
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I) :
    CategoryTheory.GlueData Scheme :=
  AllCharacteristics.OverlapComposition.glueData
    (fun ij => C.projectiveSectionLocalZeroSubscheme base M ij)
    (fun ij kl => C.projectiveSectionLocalZeroOverlap base M ij kl)
    (fun ij kl => C.projectiveSectionLocalZeroOverlapι base M ij kl)
    (fun ij kl => C.projectiveSectionLocalZeroOverlapRightMap base M ij kl)
    (fun ij kl => (C.projectiveSectionLocalZeroOverlapSwap base M ij kl).hom)
    (fun ij kl =>
      C.projectiveSectionLocalZeroOverlapSwap_hom_comp_left_eq_rightMap
        base M ij kl)
    (fun ij jk kl => C.projectiveSectionLocalZeroTripleCross base M ij jk kl)
    (fun ij jk kl =>
      C.projectiveSectionLocalZeroTripleCross_fac base M ij jk kl)
    (fun ij jk kl =>
      C.projectiveSectionLocalZeroTripleCross_right base M ij jk kl)
    (fun ij kl =>
      C.projectiveSectionLocalZeroOverlapSwap_hom_comp_swap_hom
        base M ij kl)
    (fun ij => C.projectiveSectionLocalZeroOverlapSwap_self base M ij)

/-- The categorical universal-zero overlap datum is scheme gluing data,
because every overlap inclusion is an open immersion. -/
noncomputable def projectiveSectionLocalZeroSchemeGlueData
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I) :
    Scheme.GlueData where
  toGlueData := C.projectiveSectionLocalZeroCategoryGlueData base M
  f_open ij kl :=
    C.isOpenImmersion_projectiveSectionLocalZeroOverlapι base M ij kl

/-- The global universal zero scheme obtained by gluing its affine product
chart zero loci. -/
noncomputable def projectiveSectionLocalZeroGluedScheme
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I) :
    Scheme :=
  (C.projectiveSectionLocalZeroSchemeGlueData base M).glued

/-- A local universal zero locus as an open chart in the glued global zero
scheme. -/
noncomputable def projectiveSectionLocalZeroGluedι
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroSubscheme base M ij ⟶
      C.projectiveSectionLocalZeroGluedScheme base M :=
  (C.projectiveSectionLocalZeroSchemeGlueData base M).ι ij

/-- Every local zero-locus chart maps openly into the glued global zero
scheme. -/
instance isOpenImmersion_projectiveSectionLocalZeroGluedι
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    IsOpenImmersion (C.projectiveSectionLocalZeroGluedι base M ij) :=
  Scheme.GlueData.ι_isOpenImmersion
    (C.projectiveSectionLocalZeroSchemeGlueData base M) ij

/-- Compatibility of the local ambient maps in the transition-map form
required for descent through the categorical glue data. -/
theorem projectiveSectionLocalZeroToAmbient_glue_compat
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroOverlapι base M ij kl ≫
        C.projectiveSectionLocalZeroToAmbient base M ij =
      (C.projectiveSectionLocalZeroOverlapSwap base M ij kl).hom ≫
        C.projectiveSectionLocalZeroOverlapι base M kl ij ≫
        C.projectiveSectionLocalZeroToAmbient base M kl := by
  rw [← Category.assoc,
    C.projectiveSectionLocalZeroOverlapSwap_hom_comp_left_eq_rightMap
      base M ij kl]
  exact (C.projectiveSectionLocalZeroOverlapRightMap_comp_toAmbient
    base M ij kl).symm

/-- The local closed zero loci descend to a canonical map from the glued
global zero scheme to the ambient universal product. -/
noncomputable def projectiveSectionLocalZeroGluedToAmbient
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I) :
    C.projectiveSectionLocalZeroGluedScheme base M ⟶
      pullback base
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M) :=
  (C.projectiveSectionLocalZeroSchemeGlueData base M).descTo
    (fun ij => C.projectiveSectionLocalZeroToAmbient base M ij)
    (fun ij kl => C.projectiveSectionLocalZeroToAmbient_glue_compat
      base M ij kl)

/-- The descended ambient map restricts on each glued chart to the original
local closed zero-locus map. -/
theorem projectiveSectionLocalZeroGluedι_comp_toAmbient
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroGluedι base M ij ≫
        C.projectiveSectionLocalZeroGluedToAmbient base M =
      C.projectiveSectionLocalZeroToAmbient base M ij := by
  exact Scheme.GlueData.ι_descTo
    (C.projectiveSectionLocalZeroSchemeGlueData base M)
    (fun ij => C.projectiveSectionLocalZeroToAmbient base M ij)
    (fun ij kl => C.projectiveSectionLocalZeroToAmbient_glue_compat
      base M ij kl)
    ij

/-- The local zero-locus charts jointly cover the glued global zero scheme. -/
theorem projectiveSectionLocalZeroGluedι_jointly_surjective
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (x : C.projectiveSectionLocalZeroGluedScheme base M) :
    ∃ (ij : (C.projectiveSectionOpenCover base M).I₀)
      (y : C.projectiveSectionLocalZeroSubscheme base M ij),
      C.projectiveSectionLocalZeroGluedι base M ij y = x := by
  exact Scheme.GlueData.ι_jointly_surjective
    (C.projectiveSectionLocalZeroSchemeGlueData base M) x

/-- Pairwise transitions identify the local zero-locus charts in the glued
global zero scheme. -/
theorem projectiveSectionLocalZeroGluedι_glue
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    (C.projectiveSectionLocalZeroOverlapSwap base M ij kl).hom ≫
        C.projectiveSectionLocalZeroOverlapι base M kl ij ≫
        C.projectiveSectionLocalZeroGluedι base M kl =
      C.projectiveSectionLocalZeroOverlapι base M ij kl ≫
        C.projectiveSectionLocalZeroGluedι base M ij :=
  Scheme.GlueData.glue_condition
    (C.projectiveSectionLocalZeroSchemeGlueData base M) ij kl

/-- The local zero locus maps to the pullback of the glued zero scheme over
its ambient product chart. -/
noncomputable def projectiveSectionLocalZeroGluedTargetPullbackι
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroSubscheme base M ij ⟶
      pullback
        (C.projectiveSectionLocalZeroGluedToAmbient base M)
        ((C.projectiveSectionOpenCover base M).f ij) :=
  pullback.lift
    (C.projectiveSectionLocalZeroGluedι base M ij)
    (C.projectiveSectionLocalZeroIdeal base M ij).subschemeι
    (C.projectiveSectionLocalZeroGluedι_comp_toAmbient base M ij)

@[reassoc]
theorem projectiveSectionLocalZeroGluedTargetPullbackι_comp_fst
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroGluedTargetPullbackι base M ij ≫
        pullback.fst
          (C.projectiveSectionLocalZeroGluedToAmbient base M)
          ((C.projectiveSectionOpenCover base M).f ij) =
      C.projectiveSectionLocalZeroGluedι base M ij :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem projectiveSectionLocalZeroGluedTargetPullbackι_comp_snd
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroGluedTargetPullbackι base M ij ≫
        pullback.snd
          (C.projectiveSectionLocalZeroGluedToAmbient base M)
          ((C.projectiveSectionOpenCover base M).f ij) =
      (C.projectiveSectionLocalZeroIdeal base M ij).subschemeι :=
  pullback.lift_snd _ _ _

/-- A glued local chart lies over the corresponding ambient product chart. -/
theorem range_projectiveSectionLocalZeroGluedι_subset_targetPullbackFst
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    Set.range (C.projectiveSectionLocalZeroGluedι base M ij) ⊆
      Set.range (pullback.fst
        (C.projectiveSectionLocalZeroGluedToAmbient base M)
        ((C.projectiveSectionOpenCover base M).f ij)) := by
  rw [IsOpenImmersion.range_pullbackFst
    ((C.projectiveSectionOpenCover base M).f ij)
    (C.projectiveSectionLocalZeroGluedToAmbient base M)]
  rintro x ⟨y, rfl⟩
  change (C.projectiveSectionLocalZeroGluedToAmbient base M)
      (C.projectiveSectionLocalZeroGluedι base M ij y) ∈
    ((C.projectiveSectionOpenCover base M).f ij).opensRange
  rw [← Scheme.Hom.comp_apply,
    C.projectiveSectionLocalZeroGluedι_comp_toAmbient base M ij]
  exact ⟨_, rfl⟩

/-- A local zero-locus point whose ambient image lies in a second product
chart comes from the explicit pairwise zero overlap. -/
theorem exists_projectiveSectionLocalZeroOverlap_of_mem
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀)
    (y : C.projectiveSectionLocalZeroSubscheme base M ij)
    (hy : C.projectiveSectionLocalZeroToAmbient base M ij y ∈
      ((C.projectiveSectionOpenCover base M).f kl).opensRange) :
    ∃ z : C.projectiveSectionLocalZeroOverlap base M ij kl,
      C.projectiveSectionLocalZeroOverlapι base M ij kl z = y := by
  let a := pullback.fst
    ((C.projectiveSectionOpenCover base M).f ij)
    ((C.projectiveSectionOpenCover base M).f kl)
  let J := C.projectiveSectionLocalZeroIdeal base M ij
  have hmem : J.subschemeι y ∈ a.opensRange := by
    change J.subschemeι y ∈ (pullback.fst
      ((C.projectiveSectionOpenCover base M).f ij)
      ((C.projectiveSectionOpenCover base M).f kl)).opensRange
    rw [Scheme.Hom.opensRange_pullbackFst]
    exact hy
  obtain ⟨z, hz⟩ := (IsOpenImmersion.range_pullbackSnd a J.subschemeι).ge hmem
  refine ⟨(J.comapIso a).inv z, ?_⟩
  change (((J.comapIso a).inv ≫ (J.comapIso a).hom) ≫
    pullback.snd a J.subschemeι) z = y
  rw [Iso.inv_hom_id, Category.id_comp]
  exact hz

/-- Each local zero locus is the full pullback of the glued zero scheme over
its ambient product chart. -/
theorem range_projectiveSectionLocalZeroGluedTargetPullbackι_eq_univ
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    Set.range (C.projectiveSectionLocalZeroGluedTargetPullbackι base M ij) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  obtain ⟨kl, y, hy⟩ :=
    C.projectiveSectionLocalZeroGluedι_jointly_surjective base M
      (pullback.fst
        (C.projectiveSectionLocalZeroGluedToAmbient base M)
        ((C.projectiveSectionOpenCover base M).f ij) p)
  have hyUi : C.projectiveSectionLocalZeroToAmbient base M kl y ∈
      ((C.projectiveSectionOpenCover base M).f ij).opensRange := by
    rw [← C.projectiveSectionLocalZeroGluedι_comp_toAmbient base M kl]
    change (C.projectiveSectionLocalZeroGluedToAmbient base M)
      (C.projectiveSectionLocalZeroGluedι base M kl y) ∈
      ((C.projectiveSectionOpenCover base M).f ij).opensRange
    rw [hy]
    rw [← Scheme.Hom.comp_apply, pullback.condition]
    exact Scheme.Hom.mem_opensRange.mpr ⟨_, rfl⟩
  obtain ⟨w, hw⟩ :=
    C.exists_projectiveSectionLocalZeroOverlap_of_mem
      base M kl ij y hyUi
  refine ⟨C.projectiveSectionLocalZeroOverlapRightMap base M kl ij w, ?_⟩
  apply (pullback.fst
    (C.projectiveSectionLocalZeroGluedToAmbient base M)
    ((C.projectiveSectionOpenCover base M).f ij)).isEmbedding.injective
  rw [← Scheme.Hom.comp_apply,
    C.projectiveSectionLocalZeroGluedTargetPullbackι_comp_fst base M ij]
  rw [← hy, ← hw]
  change (((C.projectiveSectionLocalZeroOverlapSwap base M kl ij).hom ≫
      C.projectiveSectionLocalZeroOverlapι base M ij kl) ≫
      C.projectiveSectionLocalZeroGluedι base M ij) w =
    (C.projectiveSectionLocalZeroOverlapι base M kl ij ≫
      C.projectiveSectionLocalZeroGluedι base M kl) w
  exact congrArg (fun q => q w)
    (C.projectiveSectionLocalZeroGluedι_glue base M kl ij)

/-- The local-to-global comparison into the target pullback is an open
immersion. -/
theorem isOpenImmersion_projectiveSectionLocalZeroGluedTargetPullbackι
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    IsOpenImmersion
      (C.projectiveSectionLocalZeroGluedTargetPullbackι base M ij) := by
  let hrange : Set.range
      (C.projectiveSectionLocalZeroGluedι base M ij) ⊆
      Set.range (pullback.fst
        (C.projectiveSectionLocalZeroGluedToAmbient base M)
        ((C.projectiveSectionOpenCover base M).f ij)) :=
    C.range_projectiveSectionLocalZeroGluedι_subset_targetPullbackFst
      base M ij
  let l := IsOpenImmersion.lift
    (pullback.fst
      (C.projectiveSectionLocalZeroGluedToAmbient base M)
      ((C.projectiveSectionOpenCover base M).f ij))
    (C.projectiveSectionLocalZeroGluedι base M ij) hrange
  have hl : C.projectiveSectionLocalZeroGluedTargetPullbackι base M ij =
      l := by
    apply (cancel_mono (pullback.fst
      (C.projectiveSectionLocalZeroGluedToAmbient base M)
      ((C.projectiveSectionOpenCover base M).f ij))).mp
    rw [C.projectiveSectionLocalZeroGluedTargetPullbackι_comp_fst
      base M ij]
    exact (IsOpenImmersion.lift_fac
      (pullback.fst
        (C.projectiveSectionLocalZeroGluedToAmbient base M)
        ((C.projectiveSectionOpenCover base M).f ij))
      (C.projectiveSectionLocalZeroGluedι base M ij) hrange).symm
  rw [hl]
  change IsOpenImmersion (IsOpenImmersion.lift
    (pullback.fst
      (C.projectiveSectionLocalZeroGluedToAmbient base M)
      ((C.projectiveSectionOpenCover base M).f ij))
    (C.projectiveSectionLocalZeroGluedι base M ij) hrange)
  infer_instance

/-- The local zero locus is isomorphic to the pullback of the glued global
zero scheme over its ambient product chart. -/
theorem isIso_projectiveSectionLocalZeroGluedTargetPullbackι
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    IsIso (C.projectiveSectionLocalZeroGluedTargetPullbackι base M ij) := by
  letI : IsOpenImmersion
      (C.projectiveSectionLocalZeroGluedTargetPullbackι base M ij) :=
    C.isOpenImmersion_projectiveSectionLocalZeroGluedTargetPullbackι
      base M ij
  have hopen :
      (C.projectiveSectionLocalZeroGluedTargetPullbackι
        base M ij).opensRange = ⊤ := by
    apply TopologicalSpace.Opens.ext
    exact C.range_projectiveSectionLocalZeroGluedTargetPullbackι_eq_univ
      base M ij
  exact isIso_of_isOpenImmersion_of_opensRange_eq_top
    (C.projectiveSectionLocalZeroGluedTargetPullbackι base M ij) hopen

/-- If every scalar coordinate of the local universal section vanishes at a
field-valued ambient point, that point factors through the corresponding
local zero subscheme over the same coefficient field. -/
theorem exists_projectiveSectionLocalZero_fieldPoint_lift_of_coordinates_eq_zero
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (r : Spec (.of L) ⟶ (C.projectiveSectionOpenCover base M).X ij)
    (hzero : ∀ a : I,
      fieldPointΓevaluation r
        (BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
          (C.projectiveSectionLocalFreeIso base M ij)
          (C.projectiveSectionLocalUniversalSection base M ij) a) = 0) :
    ∃ y : Spec (.of L) ⟶
        C.projectiveSectionLocalZeroSubscheme base M ij,
      y ≫ C.projectiveSectionLocalZeroSubschemeι base M ij = r := by
  let A := (C.projectiveSectionOpenCover base M).X ij
  let J := C.projectiveSectionLocalZeroIdeal base M ij
  let x : A := r (IsLocalRing.closedPoint L)
  have hsupport : x ∈ J.support := by
    change x ∈ A.zeroLocus (↑(Ideal.span (Set.range (fun a : I =>
      BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
        (C.projectiveSectionLocalFreeIso base M ij)
        (C.projectiveSectionLocalUniversalSection base M ij) a))) :
          Set Γ(A, ⊤))
    rw [Scheme.mem_zeroLocus_iff]
    intro f hf
    apply (A.evaluation_eq_zero_iff_notMem_basicOpen
      (U := (⊤ : A.Opens)) x (Set.mem_univ x) f).mp
    change f ∈ RingHom.ker (A.Γevaluation x).hom
    apply (Ideal.span_le.mpr ?_) hf
    rintro _ ⟨a, rfl⟩
    exact Γevaluation_eq_zero_of_fieldPointΓevaluation_eq_zero r _ (hzero a)
  have hrange : x ∈ Set.range J.subschemeι := by
    rw [J.range_subschemeι]
    exact hsupport
  let y₀ : Spec (.of ((Spec (.of L)).residueField
      (IsLocalRing.closedPoint L : Spec (.of L)))) ⟶ J.subscheme :=
    closedImmersionFieldPointLiftOfMemRange J.subschemeι r
      (IsLocalRing.closedPoint L) hrange
  let e := AllCharacteristics.specFieldClosedPointResidueIso L
  let y : Spec (.of L) ⟶ J.subscheme :=
    Spec.map e.toCommRingCatIso.hom ≫ y₀
  have hy₀ : y₀ ≫ J.subschemeι =
      (Spec (.of L)).fromSpecResidueField
        (IsLocalRing.closedPoint L : Spec (.of L)) ≫ r :=
    closedImmersionFieldPointLiftOfMemRange_comp J.subschemeι r
      (IsLocalRing.closedPoint L : Spec (.of L)) hrange
  have hresidue : Spec.map e.toCommRingCatIso.hom ≫
      (Spec (.of L)).fromSpecResidueField
        (IsLocalRing.closedPoint L : Spec (.of L)) =
      𝟙 (Spec (.of L)) := by
    have hsymm :=
      AllCharacteristics.specFieldClosedPointResidueIso_symm_specMap L
    change Spec.map e.toCommRingCatIso.inv =
      (Spec (.of L)).fromSpecResidueField
        (IsLocalRing.closedPoint L : Spec (.of L)) at hsymm
    rw [← hsymm, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  refine ⟨y, ?_⟩
  change y ≫ J.subschemeι = r
  calc
    y ≫ J.subschemeι =
        Spec.map e.toCommRingCatIso.hom ≫
          (y₀ ≫ J.subschemeι) := Category.assoc _ _ _
    _ = Spec.map e.toCommRingCatIso.hom ≫
          ((Spec (.of L)).fromSpecResidueField
            (IsLocalRing.closedPoint L : Spec (.of L)) ≫ r) :=
      congrArg (fun q => Spec.map e.toCommRingCatIso.hom ≫ q) hy₀
    _ = (Spec.map e.toCommRingCatIso.hom ≫
          (Spec (.of L)).fromSpecResidueField
            (IsLocalRing.closedPoint L : Spec (.of L))) ≫ r :=
      (Category.assoc _ _ _).symm
    _ = r := by rw [hresidue, Category.id_comp]

/-- Coordinate-wise vanishing also gives a field-valued point of the globally
glued universal zero scheme.  Its ambient image is the original point of the
chosen surface--parameter chart. -/
theorem exists_projectiveSectionLocalZeroGlued_fieldPoint_lift_of_coordinates_eq_zero
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (r : Spec (.of L) ⟶ (C.projectiveSectionOpenCover base M).X ij)
    (hzero : ∀ a : I,
      fieldPointΓevaluation r
        (BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
          (C.projectiveSectionLocalFreeIso base M ij)
          (C.projectiveSectionLocalUniversalSection base M ij) a) = 0) :
    ∃ y : Spec (.of L) ⟶
        C.projectiveSectionLocalZeroGluedScheme base M,
      y ≫ C.projectiveSectionLocalZeroGluedToAmbient base M =
        r ≫ (C.projectiveSectionOpenCover base M).f ij := by
  obtain ⟨y, hy⟩ :=
    C.exists_projectiveSectionLocalZero_fieldPoint_lift_of_coordinates_eq_zero
      base M ij r hzero
  refine ⟨y ≫ C.projectiveSectionLocalZeroGluedι base M ij, ?_⟩
  calc
    (y ≫ C.projectiveSectionLocalZeroGluedι base M ij) ≫
        C.projectiveSectionLocalZeroGluedToAmbient base M =
      y ≫ (C.projectiveSectionLocalZeroGluedι base M ij ≫
        C.projectiveSectionLocalZeroGluedToAmbient base M) :=
      Category.assoc _ _ _
    _ = y ≫ C.projectiveSectionLocalZeroToAmbient base M ij := by
      rw [C.projectiveSectionLocalZeroGluedι_comp_toAmbient base M ij]
    _ = (y ≫ C.projectiveSectionLocalZeroSubschemeι base M ij) ≫
        (C.projectiveSectionOpenCover base M).f ij := rfl
    _ = r ≫ (C.projectiveSectionOpenCover base M).f ij := by rw [hy]

/-- Local coordinate-vanishing certificates for every marked field-valued
point assemble into the common family of glued zero-scheme lifts required by
the fixed-linear-system descent endpoint. -/
theorem exists_projectiveSectionLocalZeroGlued_lifts_of_local_coordinates_eq_zero
    {K L : Type u} [Field K] [Field L]
    {A Q : Scheme.{u}}
    (base : A ⟶ Spec (.of K)) [IsSeparated base] (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (qBase : Q ⟶ Spec (.of K))
    (n : ℕ) (marked : Fin n → (Q ⟶ A))
    (hmarked : ∀ i, marked i ≫ base = qBase)
    (r : Spec (.of L) ⟶ Q)
    (t : Spec (.of L) ⟶
      schemeModuleGlobalSectionsProjectiveParameters base M)
    (hrt : r ≫ qBase = t ≫
      schemeModuleGlobalSectionsProjectiveParametersToBase base M)
    (hlocal : ∀ i : Fin n,
      ∃ (ij : (C.projectiveSectionOpenCover base M).I₀)
        (ri : Spec (.of L) ⟶
          (C.projectiveSectionOpenCover base M).X ij),
        ri ≫ (C.projectiveSectionOpenCover base M).f ij =
          pullback.lift r t hrt ≫
            fixedLinearSystemIncidenceMap qBase base
              (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
              marked hmarked i ∧
        ∀ a : I,
          fieldPointΓevaluation ri
            (BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
              (C.projectiveSectionLocalFreeIso base M ij)
              (C.projectiveSectionLocalUniversalSection base M ij) a) = 0) :
    ∃ lift : Fin n → (Spec (.of L) ⟶
        C.projectiveSectionLocalZeroGluedScheme base M),
      ∀ i, lift i ≫
        C.projectiveSectionLocalZeroGluedToAmbient base M =
          pullback.lift r t hrt ≫
            fixedLinearSystemIncidenceMap qBase base
              (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
              marked hmarked i := by
  classical
  choose ij ri hri hzero using hlocal
  have hexists : ∀ i : Fin n,
      ∃ y : Spec (.of L) ⟶
          C.projectiveSectionLocalZeroGluedScheme base M,
        y ≫ C.projectiveSectionLocalZeroGluedToAmbient base M =
          pullback.lift r t hrt ≫
            fixedLinearSystemIncidenceMap qBase base
              (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
              marked hmarked i := by
    intro i
    obtain ⟨y, hy⟩ :=
      C.exists_projectiveSectionLocalZeroGlued_fieldPoint_lift_of_coordinates_eq_zero
        base M (ij i) (ri i) (hzero i)
    exact ⟨y, hy.trans (hri i)⟩
  choose lift hlift using hexists
  exact ⟨lift, hlift⟩

/-- A field-valued point of the glued zero scheme whose ambient image has
been lifted to one product chart lifts uniquely to the corresponding local
zero subscheme.  This morphism-level form retains the chosen residue field,
which is needed to compare the coefficient vector at several marked points. -/
theorem exists_projectiveSectionLocalZero_fieldPoint_lift
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (l : Spec (.of L) ⟶ C.projectiveSectionLocalZeroGluedScheme base M)
    (a : Spec (.of L) ⟶ (C.projectiveSectionOpenCover base M).X ij)
    (ha : l ≫ C.projectiveSectionLocalZeroGluedToAmbient base M =
      a ≫ (C.projectiveSectionOpenCover base M).f ij) :
    ∃ y : Spec (.of L) ⟶ C.projectiveSectionLocalZeroSubscheme base M ij,
      y ≫ C.projectiveSectionLocalZeroGluedι base M ij = l ∧
      y ≫ (C.projectiveSectionLocalZeroIdeal base M ij).subschemeι = a := by
  letI : IsIso
      (C.projectiveSectionLocalZeroGluedTargetPullbackι base M ij) :=
    C.isIso_projectiveSectionLocalZeroGluedTargetPullbackι base M ij
  let p : Spec (.of L) ⟶
      pullback
        (C.projectiveSectionLocalZeroGluedToAmbient base M)
        ((C.projectiveSectionOpenCover base M).f ij) :=
    pullback.lift l a ha
  let y := p ≫ inv
    (C.projectiveSectionLocalZeroGluedTargetPullbackι base M ij)
  refine ⟨y, ?_, ?_⟩
  · rw [← C.projectiveSectionLocalZeroGluedTargetPullbackι_comp_fst
      base M ij]
    simp only [y, Category.assoc, IsIso.inv_hom_id_assoc]
    exact pullback.lift_fst _ _ _
  · rw [← C.projectiveSectionLocalZeroGluedTargetPullbackι_comp_snd
      base M ij]
    simp only [y, Category.assoc, IsIso.inv_hom_id_assoc]
    exact pullback.lift_snd _ _ _

/-- Over every product chart, the pullback of the global ambient map is the
local closed zero locus. -/
theorem isClosedImmersion_projectiveSectionLocalZeroGluedTargetPullbackSnd
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    [IsIso (C.projectiveSectionLocalZeroGluedTargetPullbackι base M ij)] :
    IsClosedImmersion
      (pullback.snd
        (C.projectiveSectionLocalZeroGluedToAmbient base M)
        ((C.projectiveSectionOpenCover base M).f ij)) := by
  let E := asIso
    (C.projectiveSectionLocalZeroGluedTargetPullbackι base M ij)
  have h : pullback.snd
      (C.projectiveSectionLocalZeroGluedToAmbient base M)
      ((C.projectiveSectionOpenCover base M).f ij) =
      E.inv ≫ (C.projectiveSectionLocalZeroIdeal base M ij).subschemeι := by
    rw [← cancel_epi E.hom]
    simpa [E] using
      (C.projectiveSectionLocalZeroGluedTargetPullbackι_comp_snd
        base M ij)
  rw [h]
  infer_instance

/-- The glued universal zero scheme is a closed subscheme of the ambient
surface times the projective space of sections. -/
theorem isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I) :
    IsClosedImmersion
      (C.projectiveSectionLocalZeroGluedToAmbient base M) := by
  apply IsZariskiLocalAtTarget.of_openCover
    (C.projectiveSectionOpenCover base M)
  intro ij
  letI : IsIso
      (C.projectiveSectionLocalZeroGluedTargetPullbackι base M ij) :=
    C.isIso_projectiveSectionLocalZeroGluedTargetPullbackι base M ij
  exact C.isClosedImmersion_projectiveSectionLocalZeroGluedTargetPullbackSnd
    base M ij

/-- Every point of the glued universal zero scheme lies in a normalized local
chart and therefore carries a nonzero coefficient vector annihilating all
free coordinates of the evaluated basis sections. -/
theorem exists_localCoefficient_kernel_of_projectiveSectionLocalZeroGluedPoint
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (x : C.projectiveSectionLocalZeroGluedScheme base M) :
    ∃ (ij : (C.projectiveSectionOpenCover base M).I₀)
      (y : C.projectiveSectionLocalZeroSubscheme base M ij),
      C.projectiveSectionLocalZeroGluedι base M ij y = x ∧
      ∃ c : Fin (Module.finrank K
            (SchemeModuleGlobalSectionsOver base M)) →
          ((C.projectiveSectionOpenCover base M).X ij).residueField
            (C.projectiveSectionLocalZeroSubschemeι base M ij y),
        c ≠ 0 ∧ ∀ a : I,
          ∑ i, c i *
            ((C.projectiveSectionOpenCover base M).X ij).Γevaluation
              (C.projectiveSectionLocalZeroSubschemeι base M ij y)
              (BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
                (C.projectiveSectionLocalFreeIso base M ij)
                (BundleSectionZeroLocus.pullbackSection
                  (C.projectiveSectionOpenCoverToSurface base M ij) M
                  (BundleSectionZeroLocus.isIso_pullbackUnitComparison
                    (C.projectiveSectionOpenCoverToSurface base M ij))
                  (schemeModuleGlobalSectionsOverEquivSections base M
                    (Module.finBasis K
                      (SchemeModuleGlobalSectionsOver base M) i))) a) = 0 := by
  obtain ⟨ij, y, hy⟩ :=
    C.projectiveSectionLocalZeroGluedι_jointly_surjective base M x
  exact ⟨ij, y, hy,
    C.exists_projectiveSectionLocalCoefficient_kernel base M ij y⟩

/-- Membership in the bad locus for the actual glued universal zero family
unpacks into one common projective section parameter and, for every marked
point, an actual point of the glued zero scheme above the corresponding
surface--parameter pair. -/
theorem exists_parameter_and_projectiveSectionLocalZeroGluedPoints_of_mem_badLocus
    {K : Type u} [Field K]
    {A Q : Scheme.{u}}
    (base : A ⟶ Spec (.of K)) [IsSeparated base] (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (qBase : Q ⟶ Spec (.of K))
    {n : ℕ} (marked : Fin n → (Q ⟶ A))
    (hmarked : ∀ i, marked i ≫ base = qBase)
    {q : Q}
    (hq : q ∈ fixedLinearSystemBadLocus
      qBase base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
      marked hmarked
      (C.projectiveSectionLocalZeroGluedToAmbient base M)) :
    ∃ z : properFiniteIncidenceParameterSpace qBase
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M),
      pullback.fst qBase
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M) z = q ∧
      ∀ i, ∃ y : C.projectiveSectionLocalZeroGluedScheme base M,
        C.projectiveSectionLocalZeroGluedToAmbient base M y =
          fixedLinearSystemIncidenceMap qBase base
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
            marked hmarked i z := by
  obtain ⟨z, hzq, hz⟩ :=
    exists_parameter_of_mem_properFiniteIncidenceBadLocus
      qBase
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
      (fixedLinearSystemIncidenceMap qBase base
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
        marked hmarked)
      (Set.range (C.projectiveSectionLocalZeroGluedToAmbient base M)) hq
  refine ⟨z, hzq, ?_⟩
  intro i
  exact hz i

/-- Bad-locus membership has a common-field form: over the residue field of
the common incidence parameter, every marked surface--parameter point admits
a field-valued lift to the glued universal zero scheme. -/
theorem exists_parameter_and_commonResidueFieldZeroLifts_of_mem_badLocus
    {K : Type u} [Field K]
    {A Q : Scheme.{u}}
    (base : A ⟶ Spec (.of K)) [IsSeparated base] (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (qBase : Q ⟶ Spec (.of K))
    {n : ℕ} (marked : Fin n → (Q ⟶ A))
    (hmarked : ∀ i, marked i ≫ base = qBase)
    {q : Q}
    (hq : q ∈ fixedLinearSystemBadLocus
      qBase base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
      marked hmarked
      (C.projectiveSectionLocalZeroGluedToAmbient base M)) :
    ∃ z : properFiniteIncidenceParameterSpace qBase
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M),
      pullback.fst qBase
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M) z = q ∧
      ∃ lift : Fin n →
          (Spec (.of ((properFiniteIncidenceParameterSpace qBase
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).residueField z)) ⟶
            C.projectiveSectionLocalZeroGluedScheme base M),
        ∀ i, lift i ≫ C.projectiveSectionLocalZeroGluedToAmbient base M =
          (properFiniteIncidenceParameterSpace qBase
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).fromSpecResidueField z ≫
            fixedLinearSystemIncidenceMap qBase base
              (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
              marked hmarked i := by
  let zeroFamily := C.projectiveSectionLocalZeroGluedToAmbient base M
  let incidenceMap := fixedLinearSystemIncidenceMap qBase base
    (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
    marked hmarked
  obtain ⟨z, hzq, hz⟩ :=
    exists_parameter_of_mem_properFiniteIncidenceBadLocus
      qBase
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
      incidenceMap (Set.range zeroFamily) hq
  let _ : IsClosedImmersion zeroFamily :=
    C.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
  let lift : Fin n →
      (Spec (.of ((properFiniteIncidenceParameterSpace qBase
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).residueField z)) ⟶
        C.projectiveSectionLocalZeroGluedScheme base M) := fun i =>
    closedImmersionFieldPointLiftOfMemRange zeroFamily (incidenceMap i) z (hz i)
  refine ⟨z, hzq, lift, ?_⟩
  intro i
  exact closedImmersionFieldPointLiftOfMemRange_comp
    zeroFamily (incidenceMap i) z (hz i)

/-- The projective component of a common incidence parameter has one
normalized chart over its residue field.  In particular its normalized
coordinate functions give a single nonzero coefficient vector, shared by
all marked-point lifts lying over that incidence parameter. -/
theorem exists_commonProjectiveChart_of_incidenceParameter
    {K : Type u} [Field K]
    {A Q : Scheme.{u}}
    (base : A ⟶ Spec (.of K)) (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (qBase : Q ⟶ Spec (.of K))
    (z : properFiniteIncidenceParameterSpace qBase
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)) :
    ∃ (g : K →+*
          (properFiniteIncidenceParameterSpace qBase
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).residueField z)
      (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
      (b : finiteDimensionalProjectiveChartRing K
          (SchemeModuleGlobalSectionsOver base M) j →+*
        (properFiniteIncidenceParameterSpace qBase
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).residueField z),
      b.comp (chartBaseMap
          (finiteDimensionalProjectiveIdeal K
            (SchemeModuleGlobalSectionsOver base M)) j) = g ∧
      Spec.map (CommRingCat.ofHom b) ≫
          finiteDimensionalProjectiveChartι K
            (SchemeModuleGlobalSectionsOver base M) j =
        (properFiniteIncidenceParameterSpace qBase
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).fromSpecResidueField z ≫
          pullback.snd qBase
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M) ∧
      (fun k => b (chartCoordinate
        (finiteDimensionalProjectiveIdeal K
          (SchemeModuleGlobalSectionsOver base M)) j k)) ≠ 0 := by
  let Z := properFiniteIncidenceParameterSpace qBase
    (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
  let t : Spec (.of (Z.residueField z)) ⟶
      finiteDimensionalProjectiveParameters K
        (SchemeModuleGlobalSectionsOver base M) :=
    Z.fromSpecResidueField z ≫
      pullback.snd qBase
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
  let g : K →+* Z.residueField z :=
    (Spec.preimage (t ≫
      finiteDimensionalProjectiveParametersToBase K
        (SchemeModuleGlobalSectionsOver base M))).hom
  have ht : t ≫ finiteDimensionalProjectiveParametersToBase K
        (SchemeModuleGlobalSectionsOver base M) =
      Spec.map (CommRingCat.ofHom g) := by
    exact (Spec.map_preimage _).symm
  obtain ⟨j, b, hbbase, hbt⟩ :=
    exists_finiteDimensionalProjectiveChart_hom_eq_of_fieldPoint g t ht
  refine ⟨g, j, b, hbbase, hbt, ?_⟩
  exact finiteDimensionalProjectiveChart_coordinates_ne_zero j b

/-- Common-field lifts of all marked zeroes can be placed in local zero
charts whose projective component is one fixed normalized chart.  The
surface component may vary with the marked point, but every parameter
projection reconstructs the same chart-ring point `b`. -/
theorem exists_localZero_fieldPoint_lifts_over_commonProjectiveChart
    {K : Type u} [Field K]
    {A Q : Scheme.{u}}
    (base : A ⟶ Spec (.of K)) [IsSeparated base] (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (qBase : Q ⟶ Spec (.of K))
    {n : ℕ} (marked : Fin n → (Q ⟶ A))
    (hmarked : ∀ i, marked i ≫ base = qBase)
    (z : properFiniteIncidenceParameterSpace qBase
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M))
    (lift : Fin n →
      (Spec (.of ((properFiniteIncidenceParameterSpace qBase
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).residueField z)) ⟶
        C.projectiveSectionLocalZeroGluedScheme base M))
    (hlift : ∀ i, lift i ≫ C.projectiveSectionLocalZeroGluedToAmbient base M =
      (properFiniteIncidenceParameterSpace qBase
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).fromSpecResidueField z ≫
        fixedLinearSystemIncidenceMap qBase base
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
          marked hmarked i)
    (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
    (b : finiteDimensionalProjectiveChartRing K
        (SchemeModuleGlobalSectionsOver base M) j →+*
      (properFiniteIncidenceParameterSpace qBase
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).residueField z)
    (hbt : Spec.map (CommRingCat.ofHom b) ≫
        finiteDimensionalProjectiveChartι K
          (SchemeModuleGlobalSectionsOver base M) j =
      (properFiniteIncidenceParameterSpace qBase
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).fromSpecResidueField z ≫
        pullback.snd qBase
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M)) :
    ∀ i, ∃ (ij : (C.projectiveSectionOpenCover base M).I₀)
      (r : Spec (.of ((properFiniteIncidenceParameterSpace qBase
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).residueField z)) ⟶
        (C.projectiveSectionOpenCover base M).X ij)
      (y : Spec (.of ((properFiniteIncidenceParameterSpace qBase
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).residueField z)) ⟶
        C.projectiveSectionLocalZeroSubscheme base M ij),
      ij.2 = j ∧
      r ≫ C.projectiveSectionOpenCoverToSurface base M ij =
        (properFiniteIncidenceParameterSpace qBase
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).fromSpecResidueField z ≫
          pullback.fst qBase
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M) ≫ marked i ∧
      r ≫ C.projectiveSectionOpenCoverToParameterChart base M ij ≫
          finiteDimensionalProjectiveChartι K
            (SchemeModuleGlobalSectionsOver base M) ij.2 =
        Spec.map (CommRingCat.ofHom b) ≫
          finiteDimensionalProjectiveChartι K
            (SchemeModuleGlobalSectionsOver base M) j ∧
      y ≫ C.projectiveSectionLocalZeroGluedι base M ij = lift i ∧
      y ≫ (C.projectiveSectionLocalZeroIdeal base M ij).subschemeι = r := by
  let Z := properFiniteIncidenceParameterSpace qBase
    (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
  intro i
  let a : Spec (.of (Z.residueField z)) ⟶ A :=
    Z.fromSpecResidueField z ≫
      pullback.fst qBase
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M) ≫ marked i
  let t : Spec (.of (Z.residueField z)) ⟶
      finiteDimensionalProjectiveChart K
        (SchemeModuleGlobalSectionsOver base M) j :=
    Spec.map (CommRingCat.ofHom b)
  have hat : a ≫ base = t ≫ finiteDimensionalProjectiveChartToBase K
      (SchemeModuleGlobalSectionsOver base M) j := by
    calc
      a ≫ base = Z.fromSpecResidueField z ≫
          pullback.fst qBase
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M) ≫ qBase := by
        simp only [a, Category.assoc, hmarked i]
      _ = Z.fromSpecResidueField z ≫
          pullback.snd qBase
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M) ≫
          schemeModuleGlobalSectionsProjectiveParametersToBase base M := by
        rw [pullback.condition]
      _ = t ≫ finiteDimensionalProjectiveChartι K
            (SchemeModuleGlobalSectionsOver base M) j ≫
          schemeModuleGlobalSectionsProjectiveParametersToBase base M := by
        rw [← Category.assoc, ← hbt]
        rfl
      _ = t ≫ finiteDimensionalProjectiveChartToBase K
          (SchemeModuleGlobalSectionsOver base M) j := by
        change (t ≫ finiteDimensionalProjectiveChartι K
            (SchemeModuleGlobalSectionsOver base M) j) ≫
            finiteDimensionalProjectiveParametersToBase K
              (SchemeModuleGlobalSectionsOver base M) = _
        simpa only [Category.assoc] using congrArg (fun f => t ≫ f)
          (finiteDimensionalProjectiveChartι_toBase K
            (SchemeModuleGlobalSectionsOver base M) j)
  obtain ⟨ij, r, hij, hrsurface, hrparameter⟩ :=
    C.exists_projectiveSectionOpenCover_fieldPoint_lift base M j a t hat
  change (C.projectiveSectionOpenCover base M).I₀ at ij
  have hambient : lift i ≫ C.projectiveSectionLocalZeroGluedToAmbient base M =
      r ≫ (C.projectiveSectionOpenCover base M).f ij := by
    apply pullback.hom_ext
    · calc
        (lift i ≫ C.projectiveSectionLocalZeroGluedToAmbient base M) ≫
            pullback.fst base
              (schemeModuleGlobalSectionsProjectiveParametersToBase base M) =
          (Z.fromSpecResidueField z ≫
              fixedLinearSystemIncidenceMap qBase base
                (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
                marked hmarked i) ≫
            pullback.fst base
              (schemeModuleGlobalSectionsProjectiveParametersToBase base M) := by
          rw [hlift i]
        _ = a := by
          simp only [Category.assoc, fixedLinearSystemIncidenceMap_fst]
          rfl
        _ = r ≫ C.projectiveSectionOpenCoverToSurface base M ij := hrsurface.symm
        _ = (r ≫ (C.projectiveSectionOpenCover base M).f ij) ≫
            pullback.fst base
              (schemeModuleGlobalSectionsProjectiveParametersToBase base M) := by
          simpa only [Category.assoc] using
            (congrArg (fun f => r ≫ f)
              (C.projectiveSectionOpenCover_f_comp_ambientFst base M ij)).symm
    · calc
        (lift i ≫ C.projectiveSectionLocalZeroGluedToAmbient base M) ≫
            pullback.snd base
              (schemeModuleGlobalSectionsProjectiveParametersToBase base M) =
          (Z.fromSpecResidueField z ≫
              fixedLinearSystemIncidenceMap qBase base
                (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
                marked hmarked i) ≫
            pullback.snd base
              (schemeModuleGlobalSectionsProjectiveParametersToBase base M) := by
          rw [hlift i]
        _ = Z.fromSpecResidueField z ≫
            pullback.snd qBase
              (schemeModuleGlobalSectionsProjectiveParametersToBase base M) := by
          simp only [Category.assoc, fixedLinearSystemIncidenceMap_snd]
        _ = t ≫ finiteDimensionalProjectiveChartι K
            (SchemeModuleGlobalSectionsOver base M) j := by
          exact hbt.symm
        _ = r ≫ C.projectiveSectionOpenCoverToParameterChart base M ij ≫
            finiteDimensionalProjectiveChartι K
              (SchemeModuleGlobalSectionsOver base M) ij.2 := hrparameter.symm
        _ = (r ≫ (C.projectiveSectionOpenCover base M).f ij) ≫
            pullback.snd base
              (schemeModuleGlobalSectionsProjectiveParametersToBase base M) := by
          simpa only [Category.assoc] using
            (congrArg (fun f => r ≫ f)
              (C.projectiveSectionOpenCover_f_comp_ambientSnd base M ij)).symm
  obtain ⟨y, hyglued, hylocal⟩ :=
    C.exists_projectiveSectionLocalZero_fieldPoint_lift
      base M ij (lift i) r hambient
  exact ⟨ij, r, y, hij, hrsurface, hrparameter, hyglued, hylocal⟩

/-- Bad-locus membership supplies one nonzero normalized coefficient vector
over a common residue field which annihilates the local basis-evaluation row
at every marked point.  Although the surface chart may depend on the marked
point, the coefficient vector and its field are shared. -/
theorem exists_commonCoefficientKernel_of_mem_badLocus
    {K : Type u} [Field K]
    {A Q : Scheme.{u}}
    (base : A ⟶ Spec (.of K)) [IsSeparated base] (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (qBase : Q ⟶ Spec (.of K))
    {n : ℕ} (marked : Fin n → (Q ⟶ A))
    (hmarked : ∀ i, marked i ≫ base = qBase)
    {q : Q}
    (hq : q ∈ fixedLinearSystemBadLocus
      qBase base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
      marked hmarked
      (C.projectiveSectionLocalZeroGluedToAmbient base M)) :
    ∃ z : properFiniteIncidenceParameterSpace qBase
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M),
      pullback.fst qBase
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M) z = q ∧
      ∃ (g : K →+*
          (properFiniteIncidenceParameterSpace qBase
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).residueField z)
        (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
        (b : finiteDimensionalProjectiveChartRing K
            (SchemeModuleGlobalSectionsOver base M) j →+*
          (properFiniteIncidenceParameterSpace qBase
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).residueField z),
        b.comp (chartBaseMap
            (finiteDimensionalProjectiveIdeal K
              (SchemeModuleGlobalSectionsOver base M)) j) = g ∧
        (fun k => b (chartCoordinate
          (finiteDimensionalProjectiveIdeal K
            (SchemeModuleGlobalSectionsOver base M)) j k)) ≠ 0 ∧
        ∀ i, ∃ (ij : (C.projectiveSectionOpenCover base M).I₀)
          (r : Spec (.of ((properFiniteIncidenceParameterSpace qBase
              (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).residueField z)) ⟶
            (C.projectiveSectionOpenCover base M).X ij),
          ij.2 = j ∧
          r ≫ C.projectiveSectionOpenCoverToSurface base M ij =
            (properFiniteIncidenceParameterSpace qBase
                (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).fromSpecResidueField z ≫
              pullback.fst qBase
                (schemeModuleGlobalSectionsProjectiveParametersToBase base M) ≫ marked i ∧
          ∀ a : I,
            ∑ k, b (chartCoordinate
                (finiteDimensionalProjectiveIdeal K
                  (SchemeModuleGlobalSectionsOver base M)) j k) *
              fieldPointΓevaluation r
                (BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
                  (C.projectiveSectionLocalFreeIso base M ij)
                  (BundleSectionZeroLocus.pullbackSection
                    (C.projectiveSectionOpenCoverToSurface base M ij) M
                    (BundleSectionZeroLocus.isIso_pullbackUnitComparison
                      (C.projectiveSectionOpenCoverToSurface base M ij))
                    (schemeModuleGlobalSectionsOverEquivSections base M
                      (Module.finBasis K
                        (SchemeModuleGlobalSectionsOver base M) k))) a) = 0 := by
  obtain ⟨z, hzq, lift, hlift⟩ :=
    C.exists_parameter_and_commonResidueFieldZeroLifts_of_mem_badLocus
      base M qBase marked hmarked hq
  obtain ⟨g, j, b, hbbase, hbt, hbne⟩ :=
    exists_commonProjectiveChart_of_incidenceParameter base M qBase z
  refine ⟨z, hzq, g, j, b, hbbase, hbne, ?_⟩
  intro i
  obtain ⟨ij, r, y, hij, hrsurface, hrparameter, _hyglued, hylocal⟩ :=
    C.exists_localZero_fieldPoint_lifts_over_commonProjectiveChart
      base M qBase marked hmarked z lift hlift j b hbt i
  subst j
  have hbpre :=
    C.projectiveSectionOpenCoverToParameterChart_preimage_eq
      base M ij r b hrparameter
  refine ⟨ij, r, rfl, hrsurface, ?_⟩
  intro a
  have heq :=
    C.projectiveSectionLocalBasisCoordinate_fieldPoint_linearCombination_eq_zero
      base M ij y a
  change y ≫ C.projectiveSectionLocalZeroSubschemeι base M ij = r at hylocal
  rw [hylocal] at heq
  have hcoeff : ∀ k,
      fieldPointΓevaluation r
          (C.projectiveSectionLocalCoefficient base M ij k) =
        b (chartCoordinate
          (finiteDimensionalProjectiveIdeal K
            (SchemeModuleGlobalSectionsOver base M)) ij.2 k) := fun k =>
    C.projectiveSectionLocalCoefficient_fieldPoint_eq
      base M ij r b hbpre k
  simpa only [hcoeff] using heq

/-- The preceding incidence witnesses may simultaneously be refined to local
normalized zero charts.  Each marked point therefore comes with a local
nonzero coefficient kernel, while all witnesses retain the common global
projective parameter supplied by `z`. -/
theorem exists_parameter_and_localCoefficientKernels_of_mem_badLocus
    {K : Type u} [Field K]
    {A Q : Scheme.{u}}
    (base : A ⟶ Spec (.of K)) [IsSeparated base] (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (qBase : Q ⟶ Spec (.of K))
    {n : ℕ} (marked : Fin n → (Q ⟶ A))
    (hmarked : ∀ i, marked i ≫ base = qBase)
    {q : Q}
    (hq : q ∈ fixedLinearSystemBadLocus
      qBase base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
      marked hmarked
      (C.projectiveSectionLocalZeroGluedToAmbient base M)) :
    ∃ z : properFiniteIncidenceParameterSpace qBase
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M),
      pullback.fst qBase
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M) z = q ∧
      ∀ i, ∃ (y : C.projectiveSectionLocalZeroGluedScheme base M)
        (ij : (C.projectiveSectionOpenCover base M).I₀)
        (yij : C.projectiveSectionLocalZeroSubscheme base M ij),
        C.projectiveSectionLocalZeroGluedToAmbient base M y =
            fixedLinearSystemIncidenceMap qBase base
              (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
              marked hmarked i z ∧
        C.projectiveSectionLocalZeroGluedι base M ij yij = y ∧
        ∃ c : Fin (Module.finrank K
              (SchemeModuleGlobalSectionsOver base M)) →
            ((C.projectiveSectionOpenCover base M).X ij).residueField
              (C.projectiveSectionLocalZeroSubschemeι base M ij yij),
          c ≠ 0 ∧ ∀ a : I,
            ∑ j, c j *
              ((C.projectiveSectionOpenCover base M).X ij).Γevaluation
                (C.projectiveSectionLocalZeroSubschemeι base M ij yij)
                (BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
                  (C.projectiveSectionLocalFreeIso base M ij)
                  (BundleSectionZeroLocus.pullbackSection
                    (C.projectiveSectionOpenCoverToSurface base M ij) M
                    (BundleSectionZeroLocus.isIso_pullbackUnitComparison
                      (C.projectiveSectionOpenCoverToSurface base M ij))
                    (schemeModuleGlobalSectionsOverEquivSections base M
                      (Module.finBasis K
                        (SchemeModuleGlobalSectionsOver base M) j))) a) = 0 := by
  obtain ⟨z, hzq, hz⟩ :=
    C.exists_parameter_and_projectiveSectionLocalZeroGluedPoints_of_mem_badLocus
      base M qBase marked hmarked hq
  refine ⟨z, hzq, ?_⟩
  intro i
  obtain ⟨y, hy⟩ := hz i
  obtain ⟨ij, yij, hyij, hkernel⟩ :=
    C.exists_localCoefficient_kernel_of_projectiveSectionLocalZeroGluedPoint
      base M y
  exact ⟨y, ij, yij, hy, hyij, hkernel⟩

/-- The fixed-linear-system generic-avoidance theorem instantiated with the
actual globally glued universal zero scheme. -/
theorem genericFunctionField_avoids_projectiveSectionLocalZeroGlued
    {K P : Type u} [Field K] [Infinite P]
    {A Q : Scheme.{u}} [IsIntegral Q]
    (base : A ⟶ Spec (.of K)) [IsSeparated base] (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (qBase : Q ⟶ Spec (.of K))
    (n : ℕ) (marked : Fin n → (Q ⟶ A))
    (hmarked : ∀ i, marked i ≫ base = qBase)
    (evaluation : SchemeModuleGlobalSectionsOver base M →ₗ[K] (P → K))
    (hevaluation : Function.Injective evaluation)
    (hrank : Module.finrank K
      (SchemeModuleGlobalSectionsOver base M) ≤ n)
    (configuration : (Fin n ↪ P) → Q)
    (hbad : ∀ e : Fin n ↪ P,
      configuration e ∈ fixedLinearSystemBadLocus
        qBase base
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
        marked hmarked
        (C.projectiveSectionLocalZeroGluedToAmbient base M) →
      ∃ s : SchemeModuleGlobalSectionsOver base M,
        s ≠ 0 ∧ ∀ i, evaluation s (e i) = 0) :
    Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField) ∉
      fixedLinearSystemBadLocus
        qBase base
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
        marked hmarked
        (C.projectiveSectionLocalZeroGluedToAmbient base M) := by
  let _ : IsClosedImmersion
      (C.projectiveSectionLocalZeroGluedToAmbient base M) :=
    C.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
  exact schemeModuleGlobalSections_generic_avoids_fixedLinearSystem
    base M qBase base
    (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
    n marked hmarked
    (C.projectiveSectionLocalZeroGluedToAmbient base M)
    evaluation hevaluation hrank configuration hbad

/-- Kernel-witness form of generic avoidance for the actual glued universal
zero family.  This is the endpoint consumed by the remaining comparison
between geometric marked-point evaluations and local free coordinates. -/
theorem genericFunctionField_avoids_projectiveSectionLocalZeroGlued_of_kernelWitness
    {K P : Type u} [Field K] [Infinite P]
    {A Q : Scheme.{u}} [IsIntegral Q]
    (base : A ⟶ Spec (.of K)) [IsSeparated base] (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (qBase : Q ⟶ Spec (.of K))
    (n : ℕ) (marked : Fin n → (Q ⟶ A))
    (hmarked : ∀ i, marked i ≫ base = qBase)
    (evaluation : SchemeModuleGlobalSectionsOver base M →ₗ[K] (P → K))
    (hevaluation : Function.Injective evaluation)
    (hrank : Module.finrank K
      (SchemeModuleGlobalSectionsOver base M) ≤ n)
    (configuration : (Fin n ↪ P) → Q)
    (hkernel : ∀ e : Fin n ↪ P,
      configuration e ∈ fixedLinearSystemBadLocus
        qBase base
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
        marked hmarked
        (C.projectiveSectionLocalZeroGluedToAmbient base M) →
      ∃ (L : Type u) (_ : Field L) (g : K →+* L)
        (c : Fin (Module.finrank K
          (SchemeModuleGlobalSectionsOver base M)) → L),
        c ≠ 0 ∧
        (fun i => ∑ j, g (evaluation
          (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) j)
          (e i)) * c j) = 0) :
    Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField) ∉
      fixedLinearSystemBadLocus
        qBase base
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
        marked hmarked
        (C.projectiveSectionLocalZeroGluedToAmbient base M) := by
  let _ : IsClosedImmersion
      (C.projectiveSectionLocalZeroGluedToAmbient base M) :=
    C.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
  exact schemeModuleGlobalSections_generic_avoids_fixedLinearSystem_of_kernelWitness
    base M qBase base
    (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
    n marked hmarked
    (C.projectiveSectionLocalZeroGluedToAmbient base M)
    evaluation hevaluation hrank configuration hkernel

/-- Final comparison form of the glued universal-zero-family argument.
The compatibility hypothesis says that, after passing to the common
incidence residue field, one free coordinate of each pulled-back basis
section is the scalar extension of the concrete point-evaluation used in the
finite-dimensional argument. -/
theorem genericFunctionField_avoids_projectiveSectionLocalZeroGlued_of_localEvaluation
    {K P : Type u} [Field K] [Infinite P]
    {A Q : Scheme.{u}} [IsIntegral Q]
    (base : A ⟶ Spec (.of K)) [IsSeparated base] (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (qBase : Q ⟶ Spec (.of K))
    (n : ℕ) (marked : Fin n → (Q ⟶ A))
    (hmarked : ∀ i, marked i ≫ base = qBase)
    (evaluation : SchemeModuleGlobalSectionsOver base M →ₗ[K] (P → K))
    (hevaluation : Function.Injective evaluation)
    (hrank : Module.finrank K
      (SchemeModuleGlobalSectionsOver base M) ≤ n)
    (configuration : (Fin n ↪ P) → Q)
    (hlocalEvaluation : ∀ (e : Fin n ↪ P)
      (z : properFiniteIncidenceParameterSpace qBase
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M))
      (g : K →+*
        (properFiniteIncidenceParameterSpace qBase
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).residueField z)
      (i : Fin n)
      (ij : (C.projectiveSectionOpenCover base M).I₀)
      (r : Spec (.of ((properFiniteIncidenceParameterSpace qBase
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).residueField z)) ⟶
        (C.projectiveSectionOpenCover base M).X ij),
      r ≫ C.projectiveSectionOpenCoverToSurface base M ij =
        (properFiniteIncidenceParameterSpace qBase
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).fromSpecResidueField z ≫
          pullback.fst qBase
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M) ≫ marked i →
      ∃ a : I, ∀ k,
        fieldPointΓevaluation r
            (BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
              (C.projectiveSectionLocalFreeIso base M ij)
              (BundleSectionZeroLocus.pullbackSection
                (C.projectiveSectionOpenCoverToSurface base M ij) M
                (BundleSectionZeroLocus.isIso_pullbackUnitComparison
                  (C.projectiveSectionOpenCoverToSurface base M ij))
                (schemeModuleGlobalSectionsOverEquivSections base M
                  (Module.finBasis K
                    (SchemeModuleGlobalSectionsOver base M) k))) a) =
          g (evaluation
            (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k)
            (e i))) :
    Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField) ∉
      fixedLinearSystemBadLocus
        qBase base
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
        marked hmarked
        (C.projectiveSectionLocalZeroGluedToAmbient base M) := by
  apply C.genericFunctionField_avoids_projectiveSectionLocalZeroGlued_of_kernelWitness
    base M qBase n marked hmarked evaluation hevaluation hrank configuration
  intro e hbad
  obtain ⟨z, _hzq, g, j, b, _hbbase, hc, hrows⟩ :=
    C.exists_commonCoefficientKernel_of_mem_badLocus
      base M qBase marked hmarked hbad
  refine ⟨_, inferInstance, g,
    (fun k => b (chartCoordinate
      (finiteDimensionalProjectiveIdeal K
        (SchemeModuleGlobalSectionsOver base M)) j k)), hc, ?_⟩
  funext i
  obtain ⟨ij, r, _hij, hrsurface, hrow⟩ := hrows i
  obtain ⟨a, ha⟩ := hlocalEvaluation e z g i ij r hrsurface
  have h := hrow a
  simpa only [ha, mul_comm, Pi.zero_apply] using h

/-- Line-bundle form of the final comparison theorem.  Local coordinates
of a section depend on the chosen trivialization, so comparison with a fixed
point-evaluation functional is canonical only up to one common nonzero
scalar.  Such a row scaling does not change the kernel of the evaluation
matrix and is therefore sufficient for generic avoidance. -/
theorem genericFunctionField_avoids_projectiveSectionLocalZeroGlued_of_localEvaluation_upToUnit
    {K P : Type u} [Field K] [Infinite P]
    {A Q : Scheme.{u}} [IsIntegral Q]
    (base : A ⟶ Spec (.of K)) [IsSeparated base] (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (qBase : Q ⟶ Spec (.of K))
    (n : ℕ) (marked : Fin n → (Q ⟶ A))
    (hmarked : ∀ i, marked i ≫ base = qBase)
    (evaluation : SchemeModuleGlobalSectionsOver base M →ₗ[K] (P → K))
    (hevaluation : Function.Injective evaluation)
    (hrank : Module.finrank K
      (SchemeModuleGlobalSectionsOver base M) ≤ n)
    (configuration : (Fin n ↪ P) → Q)
    (hlocalEvaluation : ∀ (e : Fin n ↪ P)
      (z : properFiniteIncidenceParameterSpace qBase
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M))
      (g : K →+*
        (properFiniteIncidenceParameterSpace qBase
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).residueField z)
      (i : Fin n)
      (ij : (C.projectiveSectionOpenCover base M).I₀)
      (r : Spec (.of ((properFiniteIncidenceParameterSpace qBase
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).residueField z)) ⟶
        (C.projectiveSectionOpenCover base M).X ij),
      r ≫ C.projectiveSectionOpenCoverToSurface base M ij =
        (properFiniteIncidenceParameterSpace qBase
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).fromSpecResidueField z ≫
          pullback.fst qBase
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M) ≫ marked i →
      ∃ (a : I)
        (lambda : (properFiniteIncidenceParameterSpace qBase
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).residueField z),
        lambda ≠ 0 ∧ ∀ k,
          fieldPointΓevaluation r
              (BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
                (C.projectiveSectionLocalFreeIso base M ij)
                (BundleSectionZeroLocus.pullbackSection
                  (C.projectiveSectionOpenCoverToSurface base M ij) M
                  (BundleSectionZeroLocus.isIso_pullbackUnitComparison
                    (C.projectiveSectionOpenCoverToSurface base M ij))
                  (schemeModuleGlobalSectionsOverEquivSections base M
                    (Module.finBasis K
                      (SchemeModuleGlobalSectionsOver base M) k))) a) =
            lambda * g (evaluation
              (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k)
              (e i))) :
    Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField) ∉
      fixedLinearSystemBadLocus
        qBase base
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
        marked hmarked
        (C.projectiveSectionLocalZeroGluedToAmbient base M) := by
  apply C.genericFunctionField_avoids_projectiveSectionLocalZeroGlued_of_kernelWitness
    base M qBase n marked hmarked evaluation hevaluation hrank configuration
  intro e hbad
  obtain ⟨z, _hzq, g, j, b, _hbbase, hc, hrows⟩ :=
    C.exists_commonCoefficientKernel_of_mem_badLocus
      base M qBase marked hmarked hbad
  refine ⟨_, inferInstance, g,
    (fun k => b (chartCoordinate
      (finiteDimensionalProjectiveIdeal K
        (SchemeModuleGlobalSectionsOver base M)) j k)), hc, ?_⟩
  funext i
  obtain ⟨ij, r, _hij, hrsurface, hrow⟩ := hrows i
  obtain ⟨a, lambda, hlambda, ha⟩ :=
    hlocalEvaluation e z g i ij r hrsurface
  have h := hrow a
  simp only [ha] at h
  have hscaled : lambda * (∑ k, g (evaluation
      (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k)
      (e i)) * b (chartCoordinate
        (finiteDimensionalProjectiveIdeal K
          (SchemeModuleGlobalSectionsOver base M)) j k)) = 0 := by
    rw [Finset.mul_sum]
    calc
      (∑ k, lambda * (g (evaluation
          (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k)
          (e i)) * b (chartCoordinate
            (finiteDimensionalProjectiveIdeal K
              (SchemeModuleGlobalSectionsOver base M)) j k))) =
        ∑ k, b (chartCoordinate
            (finiteDimensionalProjectiveIdeal K
              (SchemeModuleGlobalSectionsOver base M)) j k) *
          (lambda * g (evaluation
            (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k)
            (e i))) := by
              apply Finset.sum_congr rfl
              intro k _
              ac_rfl
      _ = 0 := h
  simpa only [Pi.zero_apply] using
    (mul_eq_zero.mp hscaled).resolve_left hlambda

end SchemeModuleFiniteFreeAffineCover

end


end PfaffianDescent
