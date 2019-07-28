Require Export seasons.
Require Export month.



Definition month_season (m:month) : season :=
  match m with
  | January | February | March => Winter
  | April  | May  | June => Spring
  | July  | August | September => Summer
  | October | November | December => Autumn
  end.


Definition month_season' :=
 month_rec (fun _ => season)
           Winter Winter Winter
           Spring Spring Spring
           Summer Summer Summer
           Autumn Autumn Autumn.

Lemma  month_season_convertible : month_season = month_season'.
Proof refl_equal month_season.

 
