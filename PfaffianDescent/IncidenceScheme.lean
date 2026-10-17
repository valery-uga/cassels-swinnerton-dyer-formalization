import PfaffianDescent.IncidenceAtlas

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K]

noncomputable def incidenceAtlasTripleFirst (i j k : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    pullback (incidenceAtlasι K i j) (incidenceAtlasι K i k) ⟶ incidenceAtlasOverlap K (j, k) :=
  (incidenceAtlas_triple_exists K i j k).choose

lemma incidenceAtlasTripleFirst_fac (i j k : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceAtlasTripleFirst K i j k ≫ incidenceAtlasι K j k =
      pullback.fst _ _ ≫ incidenceAtlasTransition K i j ≫ incidenceAtlasι K j i :=
  (incidenceAtlas_triple_exists K i j k).choose_spec.1

lemma incidenceAtlasTripleFirst_other (i j k : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceAtlasTripleFirst K i j k ≫ incidenceAtlasTransition K j k ≫ incidenceAtlasι K k j =
      pullback.snd _ _ ≫ incidenceAtlasTransition K i k ≫ incidenceAtlasι K k i :=
  (incidenceAtlas_triple_exists K i j k).choose_spec.2

/-- The actual map between the two pullback presentations of a triple intersection. -/
noncomputable def incidenceAtlasTripleTransition (i j k : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    pullback (incidenceAtlasι K i j) (incidenceAtlasι K i k) ⟶
      pullback (incidenceAtlasι K j k) (incidenceAtlasι K j i) :=
  pullback.lift (incidenceAtlasTripleFirst K i j k)
    (pullback.fst _ _ ≫ incidenceAtlasTransition K i j)
    (by simpa only [Category.assoc] using incidenceAtlasTripleFirst_fac K i j k)

@[reassoc]
lemma incidenceAtlasTripleTransition_snd (i j k : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceAtlasTripleTransition K i j k ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ incidenceAtlasTransition K i j :=
  pullback.lift_snd _ _ _

@[reassoc]
lemma incidenceAtlasTripleTransition_other (i j k : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceAtlasTripleTransition K i j k ≫ pullback.fst _ _ ≫
      incidenceAtlasTransition K j k ≫ incidenceAtlasι K k j =
      pullback.snd _ _ ≫ incidenceAtlasTransition K i k ≫ incidenceAtlasι K k i := by
  unfold incidenceAtlasTripleTransition
  rw [pullback.lift_fst_assoc]
  exact incidenceAtlasTripleFirst_other K i j k

attribute [reassoc] incidenceAtlasTransition_inverse

/-- The three actual pullback transitions compose to the identity. -/
theorem incidenceAtlasTripleTransition_cocycle (i j k : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceAtlasTripleTransition K i j k ≫ incidenceAtlasTripleTransition K j k i ≫
      incidenceAtlasTripleTransition K k i j = 𝟙 _ := by
  apply (cancel_mono (pullback.snd (incidenceAtlasι K i j) (incidenceAtlasι K i k))).mp
  apply (cancel_mono (incidenceAtlasι K i k)).mp
  simp only [Category.assoc, Category.id_comp]
  rw [incidenceAtlasTripleTransition_snd_assoc,
    incidenceAtlasTripleTransition_other,
    incidenceAtlasTripleTransition_snd_assoc,
    incidenceAtlasTransition_inverse_assoc]
  exact pullback.condition

/-- Common-isotropic incidence charts with their actual transitions form scheme glue data. -/
noncomputable def incidenceGlueData : Scheme.GlueData.{u} where
  J := ULift.{u} (Equiv.Perm (Fin 3 ⊕ Fin 3))
  U _ := incidenceGraphScheme K
  V ij := incidenceAtlasOverlap K (ij.1.down, ij.2.down)
  f i j := incidenceAtlasι K i.down j.down
  f_id i := incidenceAtlasι_self_isIso K i.down
  f_open i j := incidenceAtlasι_isOpenImmersion K i.down j.down
  t i j := incidenceAtlasTransition K i.down j.down
  t_id i := incidenceAtlasTransition_self K i.down
  t' i j k := incidenceAtlasTripleTransition K i.down j.down k.down
  t_fac i j k := incidenceAtlasTripleTransition_snd K i.down j.down k.down
  cocycle i j k := incidenceAtlasTripleTransition_cocycle K i.down j.down k.down

/-- The global common-isotropic incidence scheme obtained by gluing the actual chart parameter schemes. -/
noncomputable def incidenceScheme : Scheme.{u} :=
  (incidenceGlueData K).glued

noncomputable def incidenceChartι (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceGraphScheme K ⟶ incidenceScheme K :=
  (incidenceGlueData K).ι (ULift.up i)

instance incidenceChartι_isOpenImmersion (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    IsOpenImmersion (incidenceChartι K i) := by
  exact Scheme.GlueData.ι_isOpenImmersion (incidenceGlueData K) (ULift.up i)

theorem incidenceChartι_jointly_surjective (x : incidenceScheme K) :
    ∃ (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) (y : incidenceGraphScheme K),
      incidenceChartι K i y = x := by
  obtain ⟨i, y, hy⟩ := Scheme.GlueData.ι_jointly_surjective (incidenceGlueData K) x
  exact ⟨i.down, y, hy⟩

lemma incidenceChartι_glue (i j : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceAtlasTransition K i j ≫ incidenceAtlasι K j i ≫ incidenceChartι K j =
      incidenceAtlasι K i j ≫ incidenceChartι K i :=
  Scheme.GlueData.glue_condition (incidenceGlueData K) (ULift.up i) (ULift.up j)

/-- The prescribed overlap is exactly the intersection of the two open charts. -/
noncomputable def incidenceChart_intersection (i j : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    IsLimit ((incidenceGlueData K).vPullbackCone (ULift.up i) (ULift.up j)) :=
  Scheme.GlueData.vPullbackConeIsLimit (incidenceGlueData K) (ULift.up i) (ULift.up j)

end
end PfaffianDescent
