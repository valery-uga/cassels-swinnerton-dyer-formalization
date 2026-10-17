import AllCharacteristics.FiniteFlatCycle

/-!
# The rank represented by a closed point

A closed point, viewed as the spectrum of its residue field, has scheme rank
exactly its residue-field degree. No separability assumption is used.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace AllCharacteristics
universe u

/-- The stalk of the spectrum of a field has length one. -/
theorem stalk_length_Spec_field (L : Type u) [Field L] (x : Spec (.of L)) :
    Module.length ((Spec (.of L)).presheaf.stalk x)
      ((Spec (.of L)).presheaf.stalk x) = 1 := by
  have hx : x = IsLocalRing.closedPoint L := Subsingleton.elim _ _
  subst x
  have h := ring_length_eq_of_ringEquiv
    (stalkClosedPointIso (.of L)).commRingCatIsoToRingEquiv
  exact h.trans (Module.length_eq_one L L)

/-- The fundamental cycle of a field spectrum is its unique point with
multiplicity one. -/
theorem fundamentalZeroCycle_Spec_field
    (L : Type u) [Field L] (x : closedPoints (Spec (.of L))) :
    fundamentalZeroCycle (Spec (.of L)) = Finsupp.single x 1 := by
  classical
  ext y
  have hy : y = x := Subsingleton.elim _ _
  subst y
  simp only [fundamentalZeroCycle_apply, stalk_length_Spec_field, ENat.toNat_one,
    Finsupp.single_eq_same]

/-- The degree of a field spectrum's fundamental cycle is the residue degree
of its unique point under the chosen structure morphism. -/
theorem degree_fundamentalZeroCycle_Spec_field
    {L : Type u} [Field L] {Y : Scheme.{u}} (f : Spec (.of L) ⟶ Y) :
    EffectiveZeroCycle.degree f (fundamentalZeroCycle (Spec (.of L))) =
      f.residueDegree (IsLocalRing.closedPoint L) := by
  let x : closedPoints (Spec (.of L)) := ⟨IsLocalRing.closedPoint L, isClosed_singleton⟩
  rw [fundamentalZeroCycle_Spec_field L x]
  simp [EffectiveZeroCycle.degree, x]

/-- For a finite map between field spectra, the scheme rank is the degree of
the unique residue-field extension. -/
theorem finrank_Spec_field_eq_residueDegree
    {k L : Type u} [Field k] [Field L] (f : Spec (.of L) ⟶ Spec (.of k)) [IsFinite f] :
    f.finrank (IsLocalRing.closedPoint k) = f.residueDegree (IsLocalRing.closedPoint L) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have hfin : φ.hom.Finite := (IsFinite.SpecMap_iff φ).mp inferInstance
  algebraize [φ.hom]
  have hr : (Spec.map φ).finrank (IsLocalRing.closedPoint k) = Module.finrank k L := by
    change (Spec.map (CommRingCat.ofHom (algebraMap k L))).finrank _ = _
    rw [Scheme.Hom.finrank_SpecMap_algebraMap]
    exact congrFun (Module.rankAtStalk_eq_finrank_of_free (R := k) (M := L)) _
  exact hr.trans (fundamentalZeroCycle_degree_affine (k := k) (A := L)).symm |>.trans
    (degree_fundamentalZeroCycle_Spec_field (Spec.map φ))

/-- The finite scheme associated with a point has rank equal to the full
residue degree of that point. In particular this applies to inseparable closed
points of a finite-type scheme over a field. -/
theorem finiteSchemeRank_fromSpecResidueField
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X)
    [IsFinite (X.fromSpecResidueField x ≫ f)] :
    finiteSchemeRank (X.fromSpecResidueField x ≫ f) = f.residueDegree x := by
  let p := IsLocalRing.closedPoint (X.residueField x)
  have : IsIso ((X.fromSpecResidueField x).residueFieldMap p) :=
    isIso_residueFieldMap_of_surjectiveOnStalks (X.fromSpecResidueField x) p
  have h₁ := finiteSchemeRank_eq_finrank (X.fromSpecResidueField x ≫ f)
  have h₂ := finrank_Spec_field_eq_residueDegree
    (k := k) (L := X.residueField x) (X.fromSpecResidueField x ≫ f)
  have h₃ := residueDegree_comp_of_residueFieldMap_isIso
    (X.fromSpecResidueField x) f p
  have h₄ := congrArg f.residueDegree (Scheme.fromSpecResidueField_apply x p)
  exact h₁.trans (h₂.trans (h₃.trans h₄))

/-- A closed point of a scheme locally of finite type over a field is finite
when viewed as a scheme over that field. -/
instance isFinite_closedPointToBase
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : closedPoints X) :
    IsFinite (X.fromSpecResidueField x.1 ≫ f) := by
  have : IsClosedImmersion (X.fromSpecResidueField x.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp x.2
  exact (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace
    (f := X.fromSpecResidueField x.1 ≫ f)).mpr inferInstance

/-- The rank of a closed point on a scheme locally of finite type over a field
is its full residue-field degree, including its inseparable degree. -/
theorem closedPoint_finiteSchemeRank_eq_residueDegree
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : closedPoints X) :
    finiteSchemeRank (X.fromSpecResidueField x.1 ≫ f) = f.residueDegree x.1 :=
  finiteSchemeRank_fromSpecResidueField f x.1

end AllCharacteristics
