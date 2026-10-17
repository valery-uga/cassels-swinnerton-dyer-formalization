import PfaffianDescent.MonomialCoefficientAmbientAtlas300

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- Ordinary projection comparison before any actual glued ambient is substituted. -/
private lemma nativeChartAmbientProjectionCompare305
    {C : Type*} [Category C] {Q X Xi B Bi T H E : C}
    (d : Q ⟶ X) (a : Q ⟶ Xi) (q : Q ⟶ T)
    (fx : X ⟶ B) (fi : Xi ⟶ Bi) (s : T ⟶ B) (p : T ⟶ Bi)
    (g : B ⟶ H) (i : Bi ⟶ H) (lx : X ⟶ E) (li : Xi ⟶ E) (h : E ⟶ H)
    (hd : d ≫ fx = q ≫ s) (ha : a ≫ fi = q ≫ p)
    (hlx : lx ≫ h = fx ≫ g) (hli : li ≫ h = fi ≫ i)
    (hs : s ≫ g = p ≫ i) : (d ≫ lx) ≫ h = (a ≫ li) ≫ h := by
  calc
    _ = (d ≫ fx) ≫ g := by rw [Category.assoc, hlx, ← Category.assoc]
    _ = (q ≫ s) ≫ g := congrArg (fun z => z ≫ g) hd
    _ = q ≫ (p ≫ i) := (Category.assoc q s g).trans (congrArg (fun z => q ≫ z) hs)
    _ = (a ≫ fi) ≫ i := (Category.assoc q p i).symm.trans (congrArg (fun z => z ≫ i) ha.symm)
    _ = _ := (Category.assoc a fi i).trans
      ((congrArg (fun z => a ≫ z) hli.symm).trans (Category.assoc a li h).symm)

variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] (m n : ℕ)
variable (g : Spec (.of A) ⟶ monomialCoefficientGluedScheme300 R m n)
variable (hg : g ≫ monomialCoefficientGluedToBase300 R m n =
  Spec.map (CommRingCat.ofHom (algebraMap R A)))

/-- Actual map of the original test polynomial ambient into SAME H-relative affine ambient. -/
def fixedBaseTestAmbientMap305 :
    Spec (.of (MvPolynomial (Fin m) A)) ⟶ monomialCoefficientAmbient300 R m n :=
  nativeAmbientChartLift300 (monomialCoefficientGluedToBase300 R m n)
    (nativePolynomialProjection300 R m) g
    (Spec.map (CommRingCat.ofHom (algebraMap R A))) hg
    (nativePolynomialScalarMap300 R A m) (nativePolynomialProjection300 A m)
    (nativePolynomialScalar_isPullback300 R A m)

lemma fixedBaseTestAmbientMap_toH305 :
    fixedBaseTestAmbientMap305 R m n g hg ≫ monomialCoefficientAmbientToH300 R m n =
      nativePolynomialProjection300 A m ≫ g :=
  nativeAmbientChartLift_fst300 _ _ _ _ _ _ _ _

lemma fixedBaseTestAmbientMap_toGround305 :
    fixedBaseTestAmbientMap305 R m n g hg ≫ monomialCoefficientAmbientToGroundAffine300 R m n =
      nativePolynomialScalarMap300 R A m :=
  nativeAmbientChartLift_snd300 _ _ _ _ _ _ _ _

/-- Its native Cartesianity is derived from the literal polynomial scalar square. -/
lemma fixedBaseTestAmbientMap_isPullback305 :
    IsPullback (fixedBaseTestAmbientMap305 R m n g hg) (nativePolynomialProjection300 A m)
      (monomialCoefficientAmbientToH300 R m n) g :=
  nativeAmbientChartLift_isPullback300 _ _ _ _ _ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- Original coefficient-point chart factorization induces the exact polynomial ambient factorization. -/
lemma fixedBaseTestAmbientMap_chartFactor305
    {T : Type u} [CommRing T] [Algebra R T]
    (i : MonomialCoefficientChartIndex300 m n) (f : A →ₐ[R] T)
    (p : UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex →ₐ[R] T)
    (hf : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ g =
      Spec.map (CommRingCat.ofHom p.toRingHom) ≫ monomialCoefficientGluedChartMap300 R m n i) :
    Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) f.toRingHom)) ≫
        fixedBaseTestAmbientMap305 R m n g hg =
      Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) p.toRingHom)) ≫
        monomialCoefficientPolynomialChartToAmbient300 R m n i := by
  apply pullback.hom_ext
  · exact nativeChartAmbientProjectionCompare305
      (C := Scheme.{u}) _ _ (nativePolynomialProjection300 T m)
      (nativePolynomialProjection300 A m)
      (nativePolynomialProjection300 (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex) m)
      (Spec.map (CommRingCat.ofHom f.toRingHom)) (Spec.map (CommRingCat.ofHom p.toRingHom))
      g (monomialCoefficientGluedChartMap300 R m n i)
      (fixedBaseTestAmbientMap305 R m n g hg)
      (monomialCoefficientPolynomialChartToAmbient300 R m n i)
      (monomialCoefficientAmbientToH300 R m n)
      (nativePolynomialMap_projection300 m f.toRingHom)
      (nativePolynomialMap_projection300 m p.toRingHom)
      (fixedBaseTestAmbientMap_toH305 R m n g hg)
      (monomialCoefficientPolynomialChartToAmbient_toH300 R m n i) hf
  · change (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) f.toRingHom)) ≫
        fixedBaseTestAmbientMap305 R m n g hg) ≫ monomialCoefficientAmbientToGroundAffine300 R m n =
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) p.toRingHom)) ≫
        monomialCoefficientPolynomialChartToAmbient300 R m n i) ≫
          monomialCoefficientAmbientToGroundAffine300 R m n
    calc
      _ = nativePolynomialScalarMap300 R T m := by
        rw [Category.assoc, fixedBaseTestAmbientMap_toGround305]
        exact nativePolynomialMap_ground300 m f
      _ = _ := by
        rw [Category.assoc, monomialCoefficientPolynomialChartToAmbient_toGround300]
        exact (nativePolynomialMap_ground300 m p).symm

end PfaffianDescent
