import AllCharacteristics.OrderedConfigurationSections
import AllCharacteristics.DisjointClosedUnion
import AllCharacteristics.ConstantCovers
import AllCharacteristics.FiniteSubschemeFromImmersion

/-! # The actual finite subscheme over an ordered configuration

The disjoint coordinate sections give a closed immersion from the constant
cover into the pulled-back family. Its structure map is finite étale of
rank exactly n, so its kernel ideal defines an actual finite-subscheme datum.
The source scheme and the embedding are retained by an explicit isomorphism.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (n : ℕ)

/-- The configuration scheme with one of its n coordinates marked. -/
noncomputable def orderedConfigurationMarkedSource : Scheme.{u} :=
  ∐ fun _ : ULift.{u} (Fin n) => (orderedFamilyConfigurationOver f n).left

/-- The union of the actual coordinate sections inside the pulled-back family. -/
noncomputable def orderedConfigurationUnionMap : orderedConfigurationMarkedSource f n ⟶
    pullback f (orderedFamilyConfigurationOver f n).hom :=
  Sigma.desc (fun i : ULift.{u} (Fin n) => orderedConfigurationSection f n i.down)

/-- The union structure map is exactly the constant cover of the configuration base. -/
lemma orderedConfigurationUnionMap_toBase :
    orderedConfigurationUnionMap f n ≫ pullback.snd f (orderedFamilyConfigurationOver f n).hom =
      constantCoverToBase (ULift.{u} (Fin n)) (orderedFamilyConfigurationOver f n).left := by
  apply Sigma.hom_ext
  intro i
  change Sigma.ι (fun _ : ULift.{u} (Fin n) => (orderedFamilyConfigurationOver f n).left) i ≫
    Sigma.desc (fun j : ULift.{u} (Fin n) => orderedConfigurationSection f n j.down) ≫
      pullback.snd f (orderedFamilyConfigurationOver f n).hom = _
  rw [← Category.assoc, Sigma.ι_desc, orderedConfigurationSection_snd]
  exact (Sigma.ι_desc (fun _ : ULift.{u} (Fin n) => 𝟙 (orderedFamilyConfigurationOver f n).left) i).symm

/-- The disjoint coordinate sections form an actual closed subscheme. -/
instance isClosedImmersion_orderedConfigurationUnionMap :
    IsClosedImmersion (orderedConfigurationUnionMap f n) := by
  apply isClosedImmersion_sigmaDesc_of_disjoint
  intro i j hij
  exact disjoint_orderedConfigurationSection_ranges f n
    (fun he => hij (ULift.ext _ _ he))

/-- The union of coordinate sections is finite over the configuration base. -/
instance isFinite_orderedConfigurationUnionToBase :
    IsFinite (orderedConfigurationUnionMap f n ≫
      pullback.snd f (orderedFamilyConfigurationOver f n).hom) := by
  rw [orderedConfigurationUnionMap_toBase]
  exact isFinite_constantCoverToBase _ _

/-- The union of distinct coordinate sections is étale over the configuration base. -/
instance etale_orderedConfigurationUnionToBase :
    Etale (orderedConfigurationUnionMap f n ≫
      pullback.snd f (orderedFamilyConfigurationOver f n).hom) := by
  rw [orderedConfigurationUnionMap_toBase]
  exact etale_constantCoverToBase _ _

/-- The union has exactly n as its rank over each configuration point. -/
lemma finrank_orderedConfigurationUnionToBase (x : (orderedFamilyConfigurationOver f n).left) :
    (orderedConfigurationUnionMap f n ≫
      pullback.snd f (orderedFamilyConfigurationOver f n).hom).finrank x = n := by
  rw [orderedConfigurationUnionMap_toBase]
  exact (finrank_constantCoverToBase (ULift.{u} (Fin n))
    (orderedFamilyConfigurationOver f n).left x).trans (by simp)

/-- The actual ideal-defined finite flat subscheme of rank n over ordered configurations. -/
noncomputable def orderedConfigurationFiniteSubscheme :
    FiniteSubschemeDatum (pullback.snd f (orderedFamilyConfigurationOver f n).hom) n :=
  finiteSubschemeDatumOfClosedImmersion (orderedConfigurationUnionMap f n)
    (pullback.snd f (orderedFamilyConfigurationOver f n).hom) n
    (finrank_orderedConfigurationUnionToBase f n)

/-- The finite-subscheme datum uses exactly the kernel of the original union immersion. -/
lemma orderedConfigurationFiniteSubscheme_ideal :
    (orderedConfigurationFiniteSubscheme f n).val = (orderedConfigurationUnionMap f n).ker := rfl

/-- The original marked configuration is isomorphic to the ideal-defined subscheme. -/
noncomputable def orderedConfigurationFiniteSubschemeIso :
    orderedConfigurationMarkedSource f n ≅ (orderedConfigurationFiniteSubscheme f n).val.subscheme :=
  finiteSubschemeDatumOfClosedImmersionIso (orderedConfigurationUnionMap f n)
    (pullback.snd f (orderedFamilyConfigurationOver f n).hom) n
    (finrank_orderedConfigurationUnionToBase f n)

/-- The isomorphism preserves the original closed immersion into the pulled-back family. -/
lemma orderedConfigurationFiniteSubschemeIso_hom_ι :
    (orderedConfigurationFiniteSubschemeIso f n).hom ≫
      (orderedConfigurationFiniteSubscheme f n).val.subschemeι = orderedConfigurationUnionMap f n :=
  finiteSubschemeDatumOfClosedImmersionIso_hom_ι (orderedConfigurationUnionMap f n)
    (pullback.snd f (orderedFamilyConfigurationOver f n).hom) n
    (finrank_orderedConfigurationUnionToBase f n)

/-- The ideal-defined ordered configuration subscheme is finite étale over
the configuration base, because its source is the disjoint union of the
coordinate sections. -/
theorem orderedConfigurationFiniteSubscheme_toBase_etale :
    Etale ((orderedConfigurationFiniteSubscheme f n).val.subschemeι ≫
      pullback.snd f (orderedFamilyConfigurationOver f n).hom) := by
  exact finiteSubschemeDatumOfClosedImmersion_toBase_etale
    (orderedConfigurationUnionMap f n)
    (pullback.snd f (orderedFamilyConfigurationOver f n).hom) n
    (finrank_orderedConfigurationUnionToBase f n)

end AllCharacteristics
