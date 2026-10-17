import PfaffianDescent.SerreExtensionFoundation
import AllCharacteristics.FiniteSubschemeFromImmersion
import AllCharacteristics.FiniteSubschemeRank
import AllCharacteristics.OverlapCompositionGluing
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
namespace PfaffianDescent.SerreExtensionData
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
variable {X : Scheme.{u}} {M : SheafOfModules.{u} X.ringCatSheaf}
  (e : SerreExtensionData X M)

/-- The map from the `i,j`--`i,k` pullback to the `j,k` overlap induced by
the common triple restriction. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapCross
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    pullback
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b) ⟶
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlap e C seed j k a b :=
  (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapPairwiseIso
    e C seed i j k a b).inv ≫
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk e C seed i j k a b

/-- The third-overlap crossing is an open immersion.  It first changes the
chosen pullback model by an isomorphism and then restricts to the `j,k`
overlap. -/
theorem SerreExtensionRankTwoAffineCover.isOpenImmersion_localPencilZeroTripleOverlapCross
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapCross e C seed i j k a b) := by
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapCross
  letI : IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapPairwiseIso
        e C seed i j k a b).inv := by
    apply IsOpenImmersion.of_isIso
  letI : IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk e C seed i j k a b) :=
    SerreExtensionRankTwoAffineCover.isOpenImmersion_localPencilZeroTripleOverlapToJk
      e C seed i j k a b
  infer_instance

/-- The third-overlap crossing is monomorphic, as required for its use as a
restriction map in subsequent descent constructions. -/
instance SerreExtensionRankTwoAffineCover.mono_localPencilZeroTripleOverlapCross
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    Mono (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapCross e C seed i j k a b) :=
  (SerreExtensionRankTwoAffineCover.isOpenImmersion_localPencilZeroTripleOverlapCross
    e C seed i j k a b).mono

theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapTransition_fac
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapPairwiseIso
      e C seed i j k a b).inv ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk e C seed i j k a b ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j k a b =
    pullback.fst
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b) ≫
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap e C seed i j a b).hom ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j i a b := by
  let E := SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapPairwiseIso
    e C seed i j k a b
  calc
    E.inv ≫ SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk e C seed i j k a b ≫
        SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j k a b =
      E.inv ≫ (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapIso
        e C seed i j k a b).hom ≫
        SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToRight e C seed i j k a b := by
        rw [SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk_comp_ι]
    _ = E.inv ≫ SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι e C seed i j k a b ≫
        SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed i j a b := by
        rw [SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapIso_hom_comp_toRight_eq_rightMap]
    _ = pullback.fst _ _ ≫ SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed i j a b := by
        rw [← SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapPairwiseIso_hom_fst]
        simp
    _ = pullback.fst _ _ ≫
        (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap e C seed i j a b).hom ≫
        SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j i a b := by
        rw [SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap_hom_comp_left_eq_rightMap]

/-- The triple-overlap map has the two-sided form required by categorical
scheme gluing: after restricting to the `j,k` overlap, it agrees with the
right map out of the `i,j` overlap. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapCross_fac
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapCross e C seed i j k a b ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j k a b =
    pullback.fst
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b) ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed i j a b := by
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapCross
  rw [Category.assoc,
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapTransition_fac,
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap_hom_comp_left_eq_rightMap]

/-- The remaining right-hand compatibility for the triple crossing is
equivalent to the equality of the two concrete maps from the common triple
restriction into the `k`-th local zero locus.  The path through `i,k` has
already been identified with `localPencilZeroTripleOverlapToK`; this lemma
isolates the path through `j,k` as the final geometric coherence statement. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapCross_right_iff_toJk_eq_toK
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapCross e C seed i j k a b ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed j k a b =
    pullback.snd
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b) ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed i k a b) ↔
    (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk e C seed i j k a b ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed j k a b =
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToK e C seed i j k a b) := by
  let E := SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapPairwiseIso
    e C seed i j k a b
  constructor
  · intro h
    calc
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk e C seed i j k a b ≫
          SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed j k a b =
        E.hom ≫ (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapCross
          e C seed i j k a b ≫
          SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed j k a b) := by
          unfold SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapCross
          simp [E]
      _ = E.hom ≫ (pullback.snd
          (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)
          (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b) ≫
          SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed i k a b) :=
        congrArg (fun z => E.hom ≫ z) h
      _ = (E.hom ≫ pullback.snd
          (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)
          (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b)) ≫
          SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed i k a b :=
        (Category.assoc _ _ _).symm
      _ = SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk
          e C seed i j k a b ≫
          SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed i k a b := by
        rw [SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapPairwiseIso_hom_snd]
      _ = SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToK
          e C seed i j k a b :=
        SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk_comp_rightMap_eq_toK
          e C seed i j k a b
  · intro h
    calc
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapCross e C seed i j k a b ≫
          SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed j k a b =
        E.inv ≫ (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk
          e C seed i j k a b ≫
          SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed j k a b) := by
          unfold SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapCross
          simp [E]
      _ = E.inv ≫ SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToK
          e C seed i j k a b := congrArg (fun z => E.inv ≫ z) h
      _ = E.inv ≫ (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk
          e C seed i j k a b ≫
          SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed i k a b) := by
          rw [SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk_comp_rightMap_eq_toK]
      _ = pullback.snd
          (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)
          (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b) ≫
          SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed i k a b := by
          rw [← SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapPairwiseIso_hom_snd]
          simp [E]

/-- The triple crossing is compatible with the right local-overlap maps.
Together with `localPencilZeroTripleOverlapCross_fac`, this supplies both
projection compatibilities required to form the gluing cocycle. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapCross_right
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapCross e C seed i j k a b ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed j k a b =
    pullback.snd
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b) ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed i k a b := by
  apply (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapCross_right_iff_toJk_eq_toK
    e C seed i j k a b).mpr
  exact SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk_comp_rightMap_eq_toK
    e C seed i j k a b

/-- The local zero loci of a Serre pencil, their pairwise overlaps, and the
proved transition maps form categorical gluing data.  In particular, all
triple-overlap cocycles are now established from the actual ideal sheaves. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroGlueData
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    GlueData Scheme :=
  AllCharacteristics.OverlapComposition.glueData
    (fun i => (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subscheme)
    (fun i j => SerreExtensionRankTwoAffineCover.localPencilZeroOverlap e C seed i j a b)
    (fun i j => SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)
    (fun i j => SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed i j a b)
    (fun i j => (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap e C seed i j a b).hom)
    (fun i j => SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap_hom_comp_left_eq_rightMap
      e C seed i j a b)
    (fun i j k => SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapCross e C seed i j k a b)
    (fun i j k => SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapCross_fac
      e C seed i j k a b)
    (fun i j k => SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapCross_right
      e C seed i j k a b)
    (fun i j => SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap_hom_comp_swap_hom
      e C seed i j a b)
    (fun i => SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap_self e C seed i a b)

/-- The categorical overlap datum is a scheme gluing datum: every overlap
inclusion is an open immersion.  This constructs the global zero scheme of a
Serre-pencil member from its actual local ideal sheaves. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroSchemeGlueData
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    Scheme.GlueData where
  toGlueData := SerreExtensionRankTwoAffineCover.localPencilZeroGlueData e C seed a b
  f_open i j :=
    SerreExtensionRankTwoAffineCover.isOpenImmersion_localPencilZeroOverlapι
      e C seed i j a b

/-- The global scheme obtained by gluing the local zero loci of a member of
the Serre pencil. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroGluedScheme
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    Scheme :=
  (SerreExtensionRankTwoAffineCover.localPencilZeroSchemeGlueData e C seed a b).glued

/-- The open chart from the local zero locus into the globally glued
Serre-pencil zero scheme. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroGluedι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subscheme ⟶
      SerreExtensionRankTwoAffineCover.localPencilZeroGluedScheme e C seed a b :=
  (SerreExtensionRankTwoAffineCover.localPencilZeroSchemeGlueData e C seed a b).ι i

instance SerreExtensionRankTwoAffineCover.isOpenImmersion_localPencilZeroGluedι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedι e C seed i a b) := by
  exact Scheme.GlueData.ι_isOpenImmersion
    (SerreExtensionRankTwoAffineCover.localPencilZeroSchemeGlueData e C seed a b) i

/-- The local zero-locus charts cover the global glued zero scheme. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroGluedι_jointly_surjective
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    (x : SerreExtensionRankTwoAffineCover.localPencilZeroGluedScheme e C seed a b) :
    ∃ (i : C.ι)
      (y : (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subscheme),
      SerreExtensionRankTwoAffineCover.localPencilZeroGluedι e C seed i a b y = x := by
  obtain ⟨i, y, hy⟩ := Scheme.GlueData.ι_jointly_surjective
    (SerreExtensionRankTwoAffineCover.localPencilZeroSchemeGlueData e C seed a b) x
  exact ⟨i, y, hy⟩

/-- The pairwise transition identifies the two local zero-locus charts in
the global Serre-pencil zero scheme. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroGluedι_glue
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap e C seed i j a b).hom ≫
        SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j i a b ≫
        SerreExtensionRankTwoAffineCover.localPencilZeroGluedι e C seed j a b =
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b ≫
        SerreExtensionRankTwoAffineCover.localPencilZeroGluedι e C seed i a b :=
  Scheme.GlueData.glue_condition
    (SerreExtensionRankTwoAffineCover.localPencilZeroSchemeGlueData e C seed a b) i j

/-- The local closed zero loci have compatible ambient maps, hence induce a
canonical morphism from their glued scheme back to the ambient scheme. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroGluedScheme e C seed a b ⟶ X := by
  fapply Multicoequalizer.desc
  · exact fun i =>
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subschemeι ≫
        (C.U i).ι
  rintro ⟨i, j⟩
  change C.ι at i j
  change
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b ≫
        (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subschemeι ≫
        (C.U i).ι =
      ((SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap e C seed i j a b).hom ≫
        SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j i a b) ≫
        (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).subschemeι ≫
        (C.U j).ι
  rw [SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap_hom_comp_left_eq_rightMap]
  exact (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap_comp_subschemeι_comp_ι
    e C seed i j a b).symm

/-- On each chart, the ambient morphism of the glued zero scheme is the
original local closed-immersion map. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroGluedι_comp_toAmbient
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroGluedι e C seed i a b ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b =
    (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subschemeι ≫
      (C.U i).ι :=
  Multicoequalizer.π_desc _ _ _ _ _

/-- The local zero locus on an ambient chart maps canonically to the
base-change of the globally glued zero scheme over that chart.  The range and
open-immersion arguments below prove that this comparison is an isomorphism,
so the locally defined construction is a global closed immersion. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subscheme ⟶
      pullback
        (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)
        (C.U i).ι :=
  pullback.lift
    (SerreExtensionRankTwoAffineCover.localPencilZeroGluedι e C seed i a b)
    (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subschemeι
    (SerreExtensionRankTwoAffineCover.localPencilZeroGluedι_comp_toAmbient e C seed i a b)

/-- The first projection of the target-pullback comparison is the original
open chart in the glued zero scheme. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι_comp_fst
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι e C seed i a b ≫
      pullback.fst
        (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)
        (C.U i).ι =
      SerreExtensionRankTwoAffineCover.localPencilZeroGluedι e C seed i a b := by
  exact pullback.lift_fst _ _ _

/-- The second projection of the target-pullback comparison is the local
closed zero-locus immersion in the ambient chart. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι_comp_snd
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι e C seed i a b ≫
      pullback.snd
        (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)
        (C.U i).ι =
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subschemeι := by
  exact pullback.lift_snd _ _ _

/-- The glued local zero chart lies over its own ambient affine chart. -/
theorem SerreExtensionRankTwoAffineCover.range_localPencilZeroGluedι_subset_targetPullbackFst
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    Set.range (SerreExtensionRankTwoAffineCover.localPencilZeroGluedι e C seed i a b) ⊆
      Set.range (pullback.fst
        (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)
        (C.U i).ι) := by
  rw [IsOpenImmersion.range_pullbackFst (C.U i).ι
    (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)]
  rintro x ⟨y, rfl⟩
  change (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedι e C seed i a b y) ∈
        (C.U i).ι.opensRange
  rw [← Scheme.Hom.comp_apply,
    SerreExtensionRankTwoAffineCover.localPencilZeroGluedι_comp_toAmbient]
  exact ⟨_, rfl⟩

/-- A point of a local zero locus whose ambient image lies in a second cover
chart comes from the corresponding overlap zero locus. -/
theorem SerreExtensionRankTwoAffineCover.exists_localPencilZeroOverlap_of_mem
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    (y : (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subscheme)
    (hy : ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subschemeι ≫
      (C.U i).ι) y ∈ C.U j) :
    ∃ z : SerreExtensionRankTwoAffineCover.localPencilZeroOverlap e C seed i j a b,
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b z = y := by
  let f : ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) ⟶ (C.U i : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left)
  let I := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b
  have hmem : I.subschemeι y ∈ f.opensRange := by
    refine ⟨⟨(I.subschemeι y).1, ?_⟩, ?_⟩
    · exact ⟨(I.subschemeι y).2, hy⟩
    · apply Subtype.ext
      simp [f]
  obtain ⟨z, hz⟩ := (IsOpenImmersion.range_pullbackSnd f I.subschemeι).ge hmem
  refine ⟨(I.comapIso f).inv z, ?_⟩
  change (((I.comapIso f).inv ≫ (I.comapIso f).hom) ≫ pullback.snd f I.subschemeι) z = y
  rw [Iso.inv_hom_id, Category.id_comp]
  exact hz

/-- Each local zero locus is the full pullback of the glued zero scheme over
its ambient affine chart.  Surjectivity follows by representing a point on an
arbitrary glued chart and transporting it across the corresponding overlap. -/
theorem SerreExtensionRankTwoAffineCover.range_localPencilZeroGluedTargetPullbackι_eq_univ
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    Set.range (SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι
      e C seed i a b) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  obtain ⟨j, y, hy⟩ :=
    SerreExtensionRankTwoAffineCover.localPencilZeroGluedι_jointly_surjective
      e C seed a b
      (pullback.fst
        (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)
        (C.U i).ι p)
  have hyUi : ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).subschemeι ≫
      (C.U j).ι) y ∈ C.U i := by
    rw [← SerreExtensionRankTwoAffineCover.localPencilZeroGluedι_comp_toAmbient]
    change (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedι e C seed j a b y) ∈ C.U i
    rw [hy]
    rw [← Scheme.Hom.comp_apply, pullback.condition]
    change (C.U i).1 ((pullback.snd
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)
      (C.U i).ι p).1)
    exact (pullback.snd
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)
      (C.U i).ι p).2
  obtain ⟨w, hw⟩ :=
    SerreExtensionRankTwoAffineCover.exists_localPencilZeroOverlap_of_mem
      e C seed j i a b y hyUi
  refine ⟨SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap
    e C seed j i a b w, ?_⟩
  apply (pullback.fst
    (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)
    (C.U i).ι).isEmbedding.injective
  rw [← Scheme.Hom.comp_apply,
    SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι_comp_fst]
  rw [← hy, ← hw]
  change (((SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap e C seed j i a b).hom ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b) ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroGluedι e C seed i a b) w =
    (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j i a b ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroGluedι e C seed j a b) w
  exact congrArg (fun φ => φ w)
    (SerreExtensionRankTwoAffineCover.localPencilZeroGluedι_glue e C seed j i a b)

/-- The local-to-global comparison into the target pullback is an open
immersion. -/
theorem SerreExtensionRankTwoAffineCover.isOpenImmersion_localPencilZeroGluedTargetPullbackι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι e C seed i a b) := by
  let hrange : Set.range (SerreExtensionRankTwoAffineCover.localPencilZeroGluedι e C seed i a b) ⊆
      Set.range (pullback.fst
        (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)
        (C.U i).ι) :=
    SerreExtensionRankTwoAffineCover.range_localPencilZeroGluedι_subset_targetPullbackFst
      e C seed i a b
  let l := IsOpenImmersion.lift
    (pullback.fst
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)
      (C.U i).ι)
    (SerreExtensionRankTwoAffineCover.localPencilZeroGluedι e C seed i a b) hrange
  have hl : SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι e C seed i a b = l := by
    apply (cancel_mono (pullback.fst
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)
      (C.U i).ι)).1
    rw [SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι_comp_fst]
    exact (IsOpenImmersion.lift_fac
      (pullback.fst
        (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)
        (C.U i).ι)
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedι e C seed i a b) hrange).symm
  rw [hl]
  change IsOpenImmersion (IsOpenImmersion.lift
    (pullback.fst
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)
      (C.U i).ι)
    (SerreExtensionRankTwoAffineCover.localPencilZeroGluedι e C seed i a b) hrange)
  infer_instance

/-- Surjectivity of the local comparison on its target pullback upgrades the
already-proved open immersion to an isomorphism. -/
theorem SerreExtensionRankTwoAffineCover.isIso_localPencilZeroGluedTargetPullbackι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hcover : Set.range
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι
        e C seed i a b) = Set.univ) :
    IsIso (SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι
      e C seed i a b) := by
  letI : IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι e C seed i a b) :=
    SerreExtensionRankTwoAffineCover.isOpenImmersion_localPencilZeroGluedTargetPullbackι
      e C seed i a b
  have hopen : (SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι
      e C seed i a b).opensRange = ⊤ := by
    apply TopologicalSpace.Opens.ext
    exact hcover
  exact isIso_of_isOpenImmersion_of_opensRange_eq_top
    (SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι e C seed i a b) hopen

/-- If the local-to-global comparison over an ambient chart is an
isomorphism, the target pullback of the glued ambient morphism is the local
closed zero locus on that chart. -/
theorem SerreExtensionRankTwoAffineCover.isClosedImmersion_targetPullbackSnd
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsIso (SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι
      e C seed i a b)] :
    IsClosedImmersion
      (pullback.snd
        (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)
        (C.U i).ι) := by
  let E := asIso (SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι
    e C seed i a b)
  have h :
      pullback.snd
        (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)
        (C.U i).ι =
      E.inv ≫ (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subschemeι := by
    rw [← cancel_epi E.hom]
    simpa [E] using
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι_comp_snd
        e C seed i a b)
  rw [h]
  infer_instance

/-- The global ambient morphism of a glued Serre-pencil zero locus is a
closed immersion as soon as its comparison with each local zero locus after
base change to the affine cover is an isomorphism.  This packages the exact
target-local descent step, leaving no implicit scheme-theoretic gluing
assumption. -/
theorem SerreExtensionRankTwoAffineCover.isClosedImmersion_localPencilZeroGluedToAmbient
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hcomparison : ∀ i, IsIso
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι e C seed i a b)) :
    IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top C.U C.covers
  intro i
  have hlocal : IsClosedImmersion
      ((SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b) ∣_
        (C.U i).ι.opensRange) :=
    (MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion)
    (morphismRestrictOpensRange
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)
      (C.U i).ι)).mpr (by
      letI : IsIso (SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι
          e C seed i a b) := hcomparison i
      exact SerreExtensionRankTwoAffineCover.isClosedImmersion_targetPullbackSnd e C seed i a b)
  rw [← Scheme.Opens.opensRange_ι (C.U i)]
  exact hlocal

/-- Surjective local comparison maps suffice for the global closed immersion:
each comparison is already an open immersion. -/
theorem SerreExtensionRankTwoAffineCover.isClosedImmersion_localPencilZeroGluedToAmbient_of_range_eq_univ
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hcover : ∀ i, Set.range
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι
        e C seed i a b) = Set.univ) :
    IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b) :=
  SerreExtensionRankTwoAffineCover.isClosedImmersion_localPencilZeroGluedToAmbient
    e C seed a b
    (fun i => SerreExtensionRankTwoAffineCover.isIso_localPencilZeroGluedTargetPullbackι
      e C seed i a b (hcover i))

/-- The schemes obtained by gluing the local pencil zero loci form a closed
subscheme of the ambient surface.  The local pullback comparison is covered
on points by the overlap construction, so no additional descent hypothesis is
needed. -/
theorem SerreExtensionRankTwoAffineCover.isClosedImmersion_localPencilZeroGluedToAmbient_of_localPencilZeroGluing
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b) :=
  SerreExtensionRankTwoAffineCover.isClosedImmersion_localPencilZeroGluedToAmbient_of_range_eq_univ
    e C seed a b
    (fun i =>
      SerreExtensionRankTwoAffineCover.range_localPencilZeroGluedTargetPullbackι_eq_univ
        e C seed i a b)

/-- The zero-locus charts form an open cover of the glued Serre-pencil
zero scheme. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroGluedOpenCover
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroGluedScheme e C seed a b).OpenCover :=
  (SerreExtensionRankTwoAffineCover.localPencilZeroSchemeGlueData e C seed a b).openCover

/-- Restricted to every zero-locus chart, the ambient map of the glued
scheme is a locally closed immersion. -/
theorem SerreExtensionRankTwoAffineCover.isImmersion_localPencilZeroGluedι_comp_toAmbient
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    IsImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedι e C seed i a b ≫
        SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b) := by
  rw [SerreExtensionRankTwoAffineCover.localPencilZeroGluedι_comp_toAmbient]
  infer_instance

/-- The cyclic transition between the two pullback models of a triple
restriction.  It is constructed through the proved universal property of the
target triple overlap, which keeps the dependent pullback data explicit. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapTransition
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    pullback
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b) ⟶
    pullback
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j k a b)
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j i a b) := by
  let E : SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlap e C seed i j k a b ≅
      pullback
        (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)
        (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b) :=
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapPairwiseIso
    e C seed i j k a b
  let H : IsPullback
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι e C seed j k i a b)
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk e C seed j k i a b)
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j k a b)
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j i a b) :=
    SerreExtensionRankTwoAffineCover.isPullback_localPencilZeroTripleOverlap_pairwise
    e C seed j k i a b
  let E' : SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlap e C seed j k i a b ≅
      pullback
        (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j k a b)
        (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j i a b) :=
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapPairwiseIso
    e C seed j k i a b
  have hfac :
      E.inv ≫ SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk
        e C seed i j k a b ≫
        SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j k a b =
      pullback.fst
        (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)
        (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b) ≫
        (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap e C seed i j a b).hom ≫
        SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j i a b := by
    exact SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapTransition_fac
      e C seed i j k a b
  let u : pullback
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b) ⟶
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlap e C seed j k a b :=
    E.inv ≫ SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk
      e C seed i j k a b
  let v : pullback
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b) ⟶
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlap e C seed j i a b :=
    pullback.fst
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b) ≫
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap e C seed i j a b).hom
  have huv : u ≫ SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j k a b =
      v ≫ SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j i a b := by
    dsimp only [u, v]
    simpa only [Category.assoc] using hfac
  exact H.lift u v huv ≫ E'.hom


theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapTransition_comp_fst
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapTransition
      e C seed i j k a b ≫
      pullback.fst
        (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j k a b)
        (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j i a b) =
    (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapPairwiseIso
      e C seed i j k a b).inv ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk
        e C seed i j k a b := by
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapTransition
  dsimp
  rw [Category.assoc,
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapPairwiseIso_hom_fst]
  simp

/-- The first projection of the cyclic transition is the named third-overlap
crossing map. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapTransition_comp_fst_eq_cross
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapTransition
      e C seed i j k a b ≫
      pullback.fst
        (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j k a b)
        (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j i a b) =
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapCross e C seed i j k a b := by
  exact SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapTransition_comp_fst
    e C seed i j k a b

theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapTransition_comp_snd
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapTransition
      e C seed i j k a b ≫
      pullback.snd
        (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j k a b)
        (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j i a b) =
      pullback.fst
        (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)
        (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b) ≫
        (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap e C seed i j a b).hom := by
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapTransition
  dsimp
  rw [Category.assoc,
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapPairwiseIso_hom_snd]
  simp

/-- A globally glued Serre-pencil zero locus which is finite flat of constant
rank over the ground field becomes an ideal-defined finite-subscheme datum.
This is the bridge from the locally constructed zero scheme of one pencil
member to the finite data used in Voisin's residual construction. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatum
    {K : Type u} [Field K] (f : X ⟶ Spec (.of K))
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)]
    [IsFinite
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [Flat
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    (n : ℕ)
    (hn : ∀ s : Spec (.of K),
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f).finrank s = n) :
    AllCharacteristics.FiniteSubschemeDatum f n :=
  AllCharacteristics.finiteSubschemeDatumOfClosedImmersion
    (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b) f n hn

/-- The finite-subscheme datum attached to a pencil member, with its closed
immersion obtained from the explicit local-to-global descent comparison.
Thus callers need only establish the genuine finite-flat conditions after the
chartwise zero loci have been identified; they do not have to reintroduce a
global closed-immersion hypothesis. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatumOfDescent
    {K : Type u} [Field K] (f : X ⟶ Spec (.of K))
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hcomparison : ∀ i, IsIso
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι e C seed i a b))
    [IsFinite
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [Flat
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    (n : ℕ)
    (hn : ∀ s : Spec (.of K),
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f).finrank s = n) :
    AllCharacteristics.FiniteSubschemeDatum f n := by
  letI : IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b) :=
    SerreExtensionRankTwoAffineCover.isClosedImmersion_localPencilZeroGluedToAmbient
      e C seed a b hcomparison
  exact SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatum
    e f C seed a b n hn

/-- A pointwise-coverage proof for the local comparison maps is sufficient to
construct the finite datum of a pencil member.  This is the form intended for
the eventual gluing proof, which establishes coverage on points before any
finite-flat calculation is made. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatumOfRange
    {K : Type u} [Field K] (f : X ⟶ Spec (.of K))
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hcover : ∀ i, Set.range
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι
        e C seed i a b) = Set.univ)
    [IsFinite
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [Flat
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    (n : ℕ)
    (hn : ∀ s : Spec (.of K),
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f).finrank s = n) :
    AllCharacteristics.FiniteSubschemeDatum f n := by
  letI : IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b) :=
    SerreExtensionRankTwoAffineCover.isClosedImmersion_localPencilZeroGluedToAmbient_of_range_eq_univ
      e C seed a b hcover
  exact SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatum
    e f C seed a b n hn

/-- The finite datum of a pencil member formed by gluing its affine zero
loci.  The local overlap calculation already supplies the global closed
immersion; the remaining hypotheses are precisely finite flatness and the
fiber rank. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatumOfGluing
    {K : Type u} [Field K] (f : X ⟶ Spec (.of K))
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsFinite
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [Flat
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    (n : ℕ)
    (hn : ∀ s : Spec (.of K),
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f).finrank s = n) :
    AllCharacteristics.FiniteSubschemeDatum f n := by
  letI : IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b) :=
    SerreExtensionRankTwoAffineCover.isClosedImmersion_localPencilZeroGluedToAmbient_of_localPencilZeroGluing
      e C seed a b
  exact SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatum
    e f C seed a b n hn

/-- The finite datum supplied by local zero-locus gluing retains the glued
scheme itself, canonically and over the ambient surface. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatumOfGluingIso
    {K : Type u} [Field K] (f : X ⟶ Spec (.of K))
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsFinite
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [Flat
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    (n : ℕ)
    (hn : ∀ s : Spec (.of K),
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f).finrank s = n) :
    SerreExtensionRankTwoAffineCover.localPencilZeroGluedScheme e C seed a b ≅
      (SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatumOfGluing
        e f C seed a b n hn).val.subscheme := by
  letI : IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b) :=
    SerreExtensionRankTwoAffineCover.isClosedImmersion_localPencilZeroGluedToAmbient_of_localPencilZeroGluing
      e C seed a b
  exact AllCharacteristics.finiteSubschemeDatumOfClosedImmersionIso
    (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b) f n hn

/-- The canonical identification of the glued zero scheme with its finite
datum commutes with the immersion into the ambient surface. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatumOfGluingIso_hom_ι
    {K : Type u} [Field K] (f : X ⟶ Spec (.of K))
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsFinite
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [Flat
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    (n : ℕ)
    (hn : ∀ s : Spec (.of K),
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f).finrank s = n) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatumOfGluingIso
      e f C seed a b n hn).hom ≫
      (SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatumOfGluing
        e f C seed a b n hn).val.subschemeι =
      SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b := by
  letI : IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b) :=
    SerreExtensionRankTwoAffineCover.isClosedImmersion_localPencilZeroGluedToAmbient_of_localPencilZeroGluing
      e C seed a b
  exact AllCharacteristics.finiteSubschemeDatumOfClosedImmersionIso_hom_ι
    (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b) f n hn

/-- The descent-based finite datum has the glued zero scheme as its literal
subscheme, with the isomorphism retained over the ambient surface. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatumOfDescentIso
    {K : Type u} [Field K] (f : X ⟶ Spec (.of K))
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hcomparison : ∀ i, IsIso
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι e C seed i a b))
    [IsFinite
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [Flat
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    (n : ℕ)
    (hn : ∀ s : Spec (.of K),
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f).finrank s = n) :
    SerreExtensionRankTwoAffineCover.localPencilZeroGluedScheme e C seed a b ≅
      (SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatumOfDescent
        e f C seed a b hcomparison n hn).val.subscheme := by
  letI : IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b) :=
    SerreExtensionRankTwoAffineCover.isClosedImmersion_localPencilZeroGluedToAmbient
      e C seed a b hcomparison
  exact AllCharacteristics.finiteSubschemeDatumOfClosedImmersionIso
    (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b) f n hn

/-- The preceding isomorphism commutes with the ambient immersion. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatumOfDescentIso_hom_ι
    {K : Type u} [Field K] (f : X ⟶ Spec (.of K))
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hcomparison : ∀ i, IsIso
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι e C seed i a b))
    [IsFinite
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [Flat
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    (n : ℕ)
    (hn : ∀ s : Spec (.of K),
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f).finrank s = n) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatumOfDescentIso
      e f C seed a b hcomparison n hn).hom ≫
      (SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatumOfDescent
        e f C seed a b hcomparison n hn).val.subschemeι =
      SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b := by
  letI : IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b) :=
    SerreExtensionRankTwoAffineCover.isClosedImmersion_localPencilZeroGluedToAmbient
      e C seed a b hcomparison
  exact AllCharacteristics.finiteSubschemeDatumOfClosedImmersionIso_hom_ι
    (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b) f n hn

/-- The glued zero scheme is canonically the closed subscheme underlying the
finite datum formed from it. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatumIso
    {K : Type u} [Field K] (f : X ⟶ Spec (.of K))
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)]
    [IsFinite
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [Flat
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    (n : ℕ)
    (hn : ∀ s : Spec (.of K),
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f).finrank s = n) :
    SerreExtensionRankTwoAffineCover.localPencilZeroGluedScheme e C seed a b ≅
      (SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatum
        e f C seed a b n hn).val.subscheme :=
  AllCharacteristics.finiteSubschemeDatumOfClosedImmersionIso
    (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b) f n hn

/-- The finite-datum presentation preserves the ambient map of the glued
Serre zero scheme. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatumIso_hom_ι
    {K : Type u} [Field K] (f : X ⟶ Spec (.of K))
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)]
    [IsFinite
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [Flat
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    (n : ℕ)
    (hn : ∀ s : Spec (.of K),
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f).finrank s = n) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatumIso
      e f C seed a b n hn).hom ≫
      (SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatum
        e f C seed a b n hn).val.subschemeι =
      SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b :=
  AllCharacteristics.finiteSubschemeDatumOfClosedImmersionIso_hom_ι
    (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b) f n hn

/-- Étaleness of a finite Serre zero locus transfers to the corresponding
ideal-defined finite-subscheme datum. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatum_toBase_etale
    {K : Type u} [Field K] (f : X ⟶ Spec (.of K))
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)]
    [IsFinite
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [Flat
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [Etale
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    (n : ℕ)
    (hn : ∀ s : Spec (.of K),
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f).finrank s = n) :
    Etale ((SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatum
      e f C seed a b n hn).val.subschemeι ≫ f) :=
  AllCharacteristics.finiteSubschemeDatumOfClosedImmersion_toBase_etale
    (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b) f n hn

/-- The finite-datum cycle of a Serre-pencil zero locus is its intrinsic
finite-scheme fundamental cycle pushed forward by the glued ambient map. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatum_cycle
    {K : Type u} [Field K] (f : X ⟶ Spec (.of K))
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)]
    [IsFinite
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [Flat
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    (n : ℕ)
    (hn : ∀ s : Spec (.of K),
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f).finrank s = n) :
    AllCharacteristics.finiteSubschemeDatumCycle f
      (SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatum
        e f C seed a b n hn) =
      AllCharacteristics.pushforwardCycle
        (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)
        (PfaffianDescent.finiteSchemeFundamentalCycle
          (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)) :=
  AllCharacteristics.finiteSubschemeDatumCycle_of_closedImmersion
    (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b) f n hn

/-- Étaleness of a glued Serre-pencil zero locus transfers directly to the
finite datum constructed from the gluing.  No separate global
closed-immersion input is needed. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatumOfGluing_toBase_etale
    {K : Type u} [Field K] (f : X ⟶ Spec (.of K))
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsFinite
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [Flat
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [Etale
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    (n : ℕ)
    (hn : ∀ s : Spec (.of K),
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f).finrank s = n) :
    Etale ((SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatumOfGluing
      e f C seed a b n hn).val.subschemeι ≫ f) := by
  letI : IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b) :=
    SerreExtensionRankTwoAffineCover.isClosedImmersion_localPencilZeroGluedToAmbient_of_localPencilZeroGluing
      e C seed a b
  exact SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatum_toBase_etale
    e f C seed a b n hn

/-- The finite-datum cycle of a glued Serre-pencil zero locus is the
fundamental cycle of the literal glued zero scheme pushed to the ambient
surface.  This is the cycle presentation used by the rank-two step. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroGluedFundamentalCycle
    {K : Type u} [Field K] (f : X ⟶ Spec (.of K))
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsFinite
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)] :
    AllCharacteristics.EffectiveZeroCycle X := by
  letI : IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b) :=
    SerreExtensionRankTwoAffineCover.isClosedImmersion_localPencilZeroGluedToAmbient_of_localPencilZeroGluing
      e C seed a b
  exact AllCharacteristics.pushforwardCycle
    (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b)
    (PfaffianDescent.finiteSchemeFundamentalCycle
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f))

theorem SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatumOfGluing_cycle
    {K : Type u} [Field K] (f : X ⟶ Spec (.of K))
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsFinite
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [Flat
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    [LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f)]
    (n : ℕ)
    (hn : ∀ s : Spec (.of K),
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b ≫ f).finrank s = n) :
    AllCharacteristics.finiteSubschemeDatumCycle f
      (SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatumOfGluing
        e f C seed a b n hn) =
      SerreExtensionRankTwoAffineCover.localPencilZeroGluedFundamentalCycle
        e f C seed a b := by
  letI : IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed a b) :=
    SerreExtensionRankTwoAffineCover.isClosedImmersion_localPencilZeroGluedToAmbient_of_localPencilZeroGluing
      e C seed a b
  simpa only [SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatumOfGluing,
    SerreExtensionRankTwoAffineCover.localPencilZeroGluedFundamentalCycle] using
    (SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatum_cycle
      e f C seed a b n hn)

end PfaffianDescent.SerreExtensionData
