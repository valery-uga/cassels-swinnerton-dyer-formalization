import PfaffianDescent.GrassmannianAtlas

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K] {m n : ℕ}

noncomputable def grassmannianAtlasTripleFirst (i j k : Equiv.Perm (Fin m ⊕ Fin n)) :
    pullback (grassmannianAtlasι K i j) (grassmannianAtlasι K i k) ⟶ grassmannianAtlasOverlap K (j, k) :=
  (grassmannianAtlas_triple_exists K i j k).choose

lemma grassmannianAtlasTripleFirst_fac (i j k : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianAtlasTripleFirst K i j k ≫ grassmannianAtlasι K j k =
      pullback.fst _ _ ≫ grassmannianAtlasTransition K i j ≫ grassmannianAtlasι K j i :=
  (grassmannianAtlas_triple_exists K i j k).choose_spec.1

lemma grassmannianAtlasTripleFirst_other (i j k : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianAtlasTripleFirst K i j k ≫ grassmannianAtlasTransition K j k ≫ grassmannianAtlasι K k j =
      pullback.snd _ _ ≫ grassmannianAtlasTransition K i k ≫ grassmannianAtlasι K k i :=
  (grassmannianAtlas_triple_exists K i j k).choose_spec.2

/-- The actual map between the two pullback presentations of a triple intersection. -/
noncomputable def grassmannianAtlasTripleTransition (i j k : Equiv.Perm (Fin m ⊕ Fin n)) :
    pullback (grassmannianAtlasι K i j) (grassmannianAtlasι K i k) ⟶
      pullback (grassmannianAtlasι K j k) (grassmannianAtlasι K j i) :=
  pullback.lift (grassmannianAtlasTripleFirst K i j k)
    (pullback.fst _ _ ≫ grassmannianAtlasTransition K i j)
    (by simpa only [Category.assoc] using grassmannianAtlasTripleFirst_fac K i j k)

@[reassoc]
lemma grassmannianAtlasTripleTransition_snd (i j k : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianAtlasTripleTransition K i j k ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ grassmannianAtlasTransition K i j :=
  pullback.lift_snd _ _ _

@[reassoc]
lemma grassmannianAtlasTripleTransition_other (i j k : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianAtlasTripleTransition K i j k ≫ pullback.fst _ _ ≫
      grassmannianAtlasTransition K j k ≫ grassmannianAtlasι K k j =
      pullback.snd _ _ ≫ grassmannianAtlasTransition K i k ≫ grassmannianAtlasι K k i := by
  unfold grassmannianAtlasTripleTransition
  rw [pullback.lift_fst_assoc]
  exact grassmannianAtlasTripleFirst_other K i j k

attribute [reassoc] grassmannianAtlasTransition_inverse

/-- The three actual pullback transitions compose to the identity. -/
theorem grassmannianAtlasTripleTransition_cocycle (i j k : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianAtlasTripleTransition K i j k ≫ grassmannianAtlasTripleTransition K j k i ≫
      grassmannianAtlasTripleTransition K k i j = 𝟙 _ := by
  apply (cancel_mono (pullback.snd (grassmannianAtlasι K i j) (grassmannianAtlasι K i k))).mp
  apply (cancel_mono (grassmannianAtlasι K i k)).mp
  simp only [Category.assoc, Category.id_comp]
  rw [grassmannianAtlasTripleTransition_snd_assoc,
    grassmannianAtlasTripleTransition_other,
    grassmannianAtlasTripleTransition_snd_assoc,
    grassmannianAtlasTransition_inverse_assoc]
  exact pullback.condition

/-- Standard graph charts with their principal-open overlaps form genuine scheme glue data. -/
noncomputable def grassmannianGlueData (m n : ℕ) : Scheme.GlueData.{u} where
  J := ULift.{u} (Equiv.Perm (Fin m ⊕ Fin n))
  U _ := grassmannianChartScheme K m n
  V ij := grassmannianAtlasOverlap K (ij.1.down, ij.2.down)
  f i j := grassmannianAtlasι K i.down j.down
  f_id i := grassmannianAtlasι_self_isIso K i.down
  f_open i j := grassmannianAtlasι_isOpenImmersion K i.down j.down
  t i j := grassmannianAtlasTransition K i.down j.down
  t_id i := grassmannianAtlasTransition_self K i.down
  t' i j k := grassmannianAtlasTripleTransition K i.down j.down k.down
  t_fac i j k := grassmannianAtlasTripleTransition_snd K i.down j.down k.down
  cocycle i j k := grassmannianAtlasTripleTransition_cocycle K i.down j.down k.down

/-- The scheme obtained by gluing all standard graph charts of the quotient Grassmannian. -/
noncomputable def grassmannianScheme (m n : ℕ) : Scheme.{u} :=
  (grassmannianGlueData K m n).glued

noncomputable def grassmannianChartι (i : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianChartScheme K m n ⟶ grassmannianScheme K m n :=
  (grassmannianGlueData K m n).ι (ULift.up i)

instance grassmannianChartι_isOpenImmersion (i : Equiv.Perm (Fin m ⊕ Fin n)) :
    IsOpenImmersion (grassmannianChartι K i) := by
  exact Scheme.GlueData.ι_isOpenImmersion (grassmannianGlueData K m n) (ULift.up i)

theorem grassmannianChartι_jointly_surjective (x : grassmannianScheme K m n) :
    ∃ (i : Equiv.Perm (Fin m ⊕ Fin n)) (y : grassmannianChartScheme K m n),
      grassmannianChartι K i y = x := by
  obtain ⟨i, y, hy⟩ := Scheme.GlueData.ι_jointly_surjective (grassmannianGlueData K m n) x
  exact ⟨i.down, y, hy⟩

lemma grassmannianChartι_glue (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianAtlasTransition K i j ≫ grassmannianAtlasι K j i ≫ grassmannianChartι K j =
      grassmannianAtlasι K i j ≫ grassmannianChartι K i :=
  Scheme.GlueData.glue_condition (grassmannianGlueData K m n) (ULift.up i) (ULift.up j)

/-- The prescribed overlap is exactly the intersection of the two open charts. -/
noncomputable def grassmannianChart_intersection (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    IsLimit ((grassmannianGlueData K m n).vPullbackCone (ULift.up i) (ULift.up j)) :=
  Scheme.GlueData.vPullbackConeIsLimit (grassmannianGlueData K m n) (ULift.up i) (ULift.up j)

end
end PfaffianDescent
