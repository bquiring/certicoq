(* Ports of programs from the 3CPS benchmark suite (test/programs/llvm-sml),
   to compare CertiRocq with MLton.  Each returns a checksum of all its
   iterations, as the SML versions in sml/ print, so that neither compiler can
   drop the work.  Integers are primitive 63-bit integers (MLton: int64).
   General recursion takes a [nat] fuel ([big]), which costs one match per
   call; SML tuples are curried arguments.  The loops of the SML versions
   run [2 ^ k] iterations, as the doubling loops here. *)

From Stdlib Require Import PrimInt63 Uint63 List.
From CertiRocq.Plugin Require Import CertiRocq.

Import ListNotations.
Open Scope uint63_scope.

Definition big : nat := Nat.pow 2 16.

(* The benchmark loops run [2 ^ k] iterations: [rep (S k) acc = rep k (rep k acc)] *)

(** * ack *)

Fixpoint ack (f : nat) (m n : int) : int :=
  match f with
  | O => 0
  | S f => if m =? 0 then n + 1 else if n =? 0 then ack f (m - 1) 1 else ack f (m - 1) (ack f m (n - 1))
  end.

Fixpoint ack_loop (k : nat) (acc : int) : int :=
  match k with
  | O => acc + ack big 3 11 + ack big 2 5
  | S k => ack_loop k (ack_loop k acc)
  end.

Definition ack_bench := ack_loop 0 0.

(** * tak *)

Fixpoint tak (f : nat) (x y z : int) : int :=
  match f with
  | O => z
  | S f => if y <? x then tak f (tak f (x - 1) y z) (tak f (y - 1) z x) (tak f (z - 1) x y) else z
  end.

Fixpoint tak_loop (k : nat) (acc : int) : int :=
  match k with
  | O => acc + tak big 14 11 0
  | S k => tak_loop k (tak_loop k acc)
  end.

Definition tak_bench := tak_loop 3 0.

(** * cpstak *)

Definition cpstak (x y z : int) : int :=
  let fix tak (f : nat) (x y z : int) (k : int -> int) : int :=
    match f with
    | O => 0
    | S f =>
        if x <=? y then k z
        else tak f (x - 1) y z (fun v1 =>
               tak f (y - 1) z x (fun v2 =>
                 tak f (z - 1) x y (fun v3 => tak f v1 v2 v3 k)))
    end in
  tak big x y z (fun a => a).

Fixpoint cpstak_loop (k : nat) (acc : int) : int :=
  match k with
  | O => acc + cpstak 14 11 0
  | S k => cpstak_loop k (cpstak_loop k acc)
  end.

Definition cpstak_bench := cpstak_loop 3 0.

(** * y-fact *)

Fixpoint ycomb (f : nat) (F : (int -> int) -> int -> int) (x : int) : int :=
  match f with
  | O => 0
  | S f => let g := fun x => ycomb f F x in F g x
  end.

Definition factY (fact : int -> int) (n : int) : int := if n =? 0 then 1 else n * fact (n - 1).

Definition fact : int -> int := ycomb big factY.

Fixpoint yfact_loop (k : nat) (acc : int) : int :=
  match k with
  | O => acc + fact 11 + fact 10
  | S k => yfact_loop k (yfact_loop k acc)
  end.

Definition yfact_bench := yfact_loop 21 0.

(** * nqueens *)

Definition length {A} (xs : list A) : int :=
  let fix lp (xs : list A) (n : int) := match xs with [] => n | _ :: r => lp r (n + 1) end in lp xs 0.

Fixpoint revAppend {A} (xs ys : list A) : list A := match xs with [] => ys | x :: xr => revAppend xr (x :: ys) end.

Definition rev {A} (xs : list A) : list A := revAppend xs [].

Definition append {A} (xs ys : list A) : list A :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | _, _ => revAppend (rev xs) ys
  end.

Definition nsoln (nq : int) : int :=
  let fix safe (x d : int) (qs : list int) : bool :=
    match qs with
    | [] => true
    | q :: l => if x =? q then false else if x =? q + d then false else if x =? q - d then false else safe x (d + 1) l
    end in
  let fix gen (f : nat) (n : int) : list (list int) :=
    match f with
    | O => []
    | S f =>
        if n =? 0 then [[]]
        else
          let bs := gen f (n - 1) in
          let fix enumerate (g : nat) (q : int) (acc : list (list int)) : list (list int) :=
            match g with
            | O => acc
            | S g =>
                if q =? 0 then acc
                else
                  let fix check (bs acc : list (list int)) : list (list int) :=
                    match bs with
                    | [] => acc
                    | b :: bs => if safe q 1 b then check bs ((q :: b) :: acc) else check bs acc
                    end in
                  let res := check bs [] in
                  enumerate g (q - 1) (append res acc)
            end in
          enumerate big nq []
    end in
  length (gen big nq).

Definition nqueens_bench := nsoln 5 + nsoln 12.

(** * filter *)

Definition filter {A} (f : A -> bool) (xs : list A) : list A :=
  let fix lp (xs ys : list A) := match xs with [] => rev ys | x :: xr => if f x then lp xr (x :: ys) else lp xr ys end in
  lp xs [].

Definition list1 := [true; false; true; true; false; false].

Definition list2 : list int := [255; 287; 288; 461; 635; 420; 950; 797; 254; 936; 370; 775; 588; 880; 367; 896; 380; 268; 504; 524; 959; 361; 743; 886; 586; 99; 318; 268; 887; 445; 56; 388; 394; 863; 3; 343; 744; 475; 526; 232; 454; 669; 568; 855; 983; 682; 478; 80; 622; 869; 892; 416; 14; 812; 658; 285; 68; 510; 650; 684; 236; 776; 73; 205; 535; 319; 63; 568; 51; 329; 704; 236; 112; 842; 561; 816; 445; 746; 492; 858; 602; 765; 574; 924; 473; 466; 111; 668; 563; 958; 47; 837; 535; 530; 239; 852; 132; 70; 0; 570; 801; 681; 39; 763; 435; 246; 914; 664; 660; 312; 61; 417; 224; 526; 120; 579; 938; 892; 861; 177; 723; 791; 636; 176; 246; 506; 687; 422; 720; 199; 324; 272; 577; 252; 493; 492; 669; 242; 769; 820; 386; 406; 552; 290; 364; 849; 689; 222; 584; 452; 691; 240; 33; 558; 889; 464; 999; 150; 296; 168; 627; 793; 437; 152; 442; 330; 384; 86; 489; 195; 363; 135; 190; 117; 203; 139; 244; 993; 744; 703; 801; 503; 123; 23; 154; 947; 770; 267; 633; 344; 821; 114; 687; 238; 902; 717; 519; 280; 775; 893; 622; 187; 280; 723; 599; 31; 239; 250; 797; 888; 959; 161; 589; 20; 466; 465; 106; 806; 169; 618; 233; 436; 19; 11; 531; 969; 115; 116; 184; 122; 816; 243; 179; 594; 58; 661; 41; 580; 691; 821; 189; 706; 825; 521; 441; 521; 416; 297; 581; 466; 499; 663; 649; 59; 420; 51; 361; 669; 472; 514; 742; 9; 575; 5; 561; 916; 840; 421; 207; 578; 146; 213; 420; 486; 955; 584; 595; 673; 959; 169; 327; 547; 392; 904; 602; 848; 218; 280; 331; 878; 388; 510; 690; 228; 927; 700; 262; 384; 651; 774; 713; 448; 881; 285; 302; 980; 512; 980; 524; 2; 444; 879; 20; 656; 831; 553; 993; 171; 96; 368; 848; 269; 437; 188; 788; 590; 976; 874; 925; 921; 533; 673; 795; 536; 890; 813; 797; 90; 615; 845; 529; 848; 568; 75; 672; 841; 564; 684; 751; 538; 740; 180; 655; 762; 1; 755; 760; 376; 650; 210; 521; 982; 317; 920; 353; 640; 661; 685; 717; 833; 477; 120; 719; 909; 116; 545; 777; 320; 25; 92; 491; 546; 126; 450; 622; 366; 862; 830; 794; 450; 818; 913; 202; 518; 865; 120; 193; 145; 759; 886; 702; 859; 63; 870; 198; 599; 859; 352; 412; 529; 899; 813; 632; 566; 777; 658; 790; 43; 919; 958; 831; 975; 579; 39; 587; 952; 292; 892; 35; 203; 568; 555; 209; 937; 298; 899; 228; 167; 67; 893; 412; 4; 702; 383; 284; 284; 491; 925; 63; 455; 681; 544; 452; 55; 119; 819; 846; 305; 598; 586; 467; 546; 901; 925; 819; 416; 651; 96; 307; 774; 212; 550; 676; 904; 156; 117; 628; 612; 113; 914; 571; 230; 426; 826; 599; 535; 1000; 906; 659; 586; 224; 890; 738; 7; 609; 674; 712; 259; 683; 751; 123; 17; 822; 275; 570; 659; 69; 835; 939; 62; 408; 690; 979; 548; 99; 996; 782; 281; 774; 445; 847; 828; 286; 711; 559; 847; 564; 303; 588; 840; 770; 993; 889; 107; 626; 658; 798; 116; 93; 688; 115; 207; 82; 292; 787; 472; 441; 701; 596; 636; 100; 931; 945; 96; 522; 50; 209; 105; 82; 983; 945; 637; 462; 508; 353; 213; 474; 419; 374; 162; 416; 837; 58; 183; 272; 745; 979; 660; 289; 939; 552; 654; 721; 490; 891; 846; 222; 351; 697; 206; 876; 955; 493; 917; 767; 144; 902; 515; 396; 503; 631; 605; 596; 966; 265; 117; 164; 266; 494; 626; 46; 589; 865; 276; 521; 374; 790; 730; 34; 778; 138; 402; 455; 194; 690; 942; 486; 943; 224; 822; 145; 178; 665; 269; 226; 167; 143; 386; 130; 211; 986; 402; 506; 495; 122; 408; 556; 488; 636; 254; 374; 952; 133; 614; 367; 1000; 501; 153; 296; 604; 157; 742; 518; 865; 794; 950; 917; 542; 225; 457; 157; 637; 673; 991; 70; 507; 393; 552; 350; 340; 207; 797; 710; 144; 205; 251; 982; 852; 528; 615; 414; 937; 274; 619; 569; 198; 720; 910; 687; 742; 988; 980; 618; 684; 223; 385; 825; 354; 785; 732; 76; 784; 724; 293; 420; 304; 0; 748; 74; 140; 684; 689; 468; 504; 535; 704; 973; 596; 984; 93; 356; 319; 441; 300; 640; 197; 506; 243; 633; 436; 955; 935; 865; 944; 643; 40; 875; 112; 708; 585; 930; 260; 774; 164; 224; 231; 236; 856; 228; 58; 565; 400; 880; 375; 229; 77; 68; 932; 810; 456; 878; 269; 628; 79; 342; 913; 365; 802; 914; 9; 935; 723; 516; 775; 814; 811; 730; 809; 573; 788; 703; 740; 484; 904; 883; 384; 440; 283; 461; 691; 153; 959; 522; 82; 118; 569; 794; 341; 24; 996; 874; 787; 194; 825; 517; 25; 603; 480; 340; 906; 642; 99; 962; 94; 854; 339; 53; 533; 201; 539; 58; 477; 829; 653; 842; 205; 96; 825; 553; 636; 319; 7; 253; 602; 56; 19; 952; 790; 743; 253; 252; 724; 594; 851; 467; 830; 506; 590; 988; 276; 428; 916; 702; 638; 34; 630; 896; 510; 406; 440; 732; 234; 242; 188; 885; 657; 452; 811; 552; 180; 340; 681; 192; 851; 540; 451; 832; 942; 416; 390; 596; 358; 571; 199; 281; 463; 946; 967; 65; 463; 780; 289; 310; 414; 838; 931; 756; 523; 984; 561; 68; 756; 870; 937; 148; 136; 614; 194; 453; 852; 334; 957; 846; 689; 168; 108; 271; 159; 956; 344; 225; 110; 151; 954; 651; 465; 248; 270; 97; 853; 101; 508; 454; 819; 293; 731; 985; 927; 53; 803; 165; 552; 146; 653; 684; 312; 950; 981; 279; 161; 700; 825; 562; 134; 14; 750; 832; 60; 164; 488; 803; 110; 225; 88; 890; 498; 607; 223; 249; 659; 490; 730; 396; 858; 883; 123; 882; 480; 604; 940; 651; 45; 280; 55; 37; 233; 695; 32; 262; 312].

Fixpoint filter_loop (k : nat) (acc : int) : int :=
  match k with
  | O => acc + length (filter (fun x => x) list1) + length (filter (fun x => x <? 500) list2)
  | S k => filter_loop k (filter_loop k acc)
  end.

Definition filter_bench := filter_loop 15 0.

(** * quicksort *)

Definition partition (pivot : int) (xs : list int) : list int * list int :=
  let fix lp (xs lte gt : list int) :=
    match xs with
    | [] => (lte, gt)
    | x :: xr => if x <=? pivot then lp xr (x :: lte) gt else lp xr lte (x :: gt)
    end in
  lp xs [] [].

Fixpoint qappend (xs ys : list int) : list int := match xs with [] => ys | x :: xr => x :: qappend xr ys end.

Fixpoint qs (f : nat) (xs : list int) : list int :=
  match f with
  | O => []
  | S f =>
      match xs with
      | [] => []
      | [x] => [x]
      | x :: xr => let '(lte, gt) := partition x xr in qappend (qs f lte) (x :: qs f gt)
      end
  end.

Definition unsorted : list int := [63; 56; 19; 73; 8; 87; 41; 4; 9; 13; 96; 39; 43; 15; 46].
Definition unsorted' : list int := [63; 56; 19; 73; 8; 60; 27; 21; 89; 18; 96; 9; 14; 57; 33; 90; 53; 90; 97; 73; 62; 58; 60; 2; 50; 1; 76; 44; 75; 5; 60; 17; 7; 96; 29; 61; 71; 88; 55; 22; 100; 10; 45; 76; 89; 81; 98; 6; 60; 31; 45; 78; 99; 98; 9; 8; 68; 49; 78; 13; 19; 64; 77; 7; 21; 21; 43; 86; 2; 59; 7; 59; 88; 38; 24; 86; 59; 38; 54; 36; 4; 66; 44; 66; 60; 98; 14; 10; 25; 73; 87; 41; 4; 9; 13; 96; 39; 43; 15; 46].
Definition unsorted'' : list int := [255; 287; 288; 461; 635; 420; 950; 797; 254; 936; 370; 775; 588; 880; 367; 896; 380; 268; 504; 524; 959; 361; 743; 886; 586; 99; 318; 268; 887; 445; 56; 388; 394; 863; 3; 343; 744; 475; 526; 232; 454; 669; 568; 855; 983; 682; 478; 80; 622; 869; 892; 416; 14; 812; 658; 285; 68; 510; 650; 684; 236; 776; 73; 205; 535; 319; 63; 568; 51; 329; 704; 236; 112; 842; 561; 816; 445; 746; 492; 858; 602; 765; 574; 924; 473; 466; 111; 668; 563; 958; 47; 837; 535; 530; 239; 852; 132; 70; 0; 570; 801; 681; 39; 763; 435; 246; 914; 664; 660; 312; 61; 417; 224; 526; 120; 579; 938; 892; 861; 177; 723; 791; 636; 176; 246; 506; 687; 422; 720; 199; 324; 272; 577; 252; 493; 492; 669; 242; 769; 820; 386; 406; 552; 290; 364; 849; 689; 222; 584; 452; 691; 240; 33; 558; 889; 464; 999; 150; 296; 168; 627; 793; 437; 152; 442; 330; 384; 86; 489; 195; 363; 135; 190; 117; 203; 139; 244; 993; 744; 703; 801; 503; 123; 23; 154; 947; 770; 267; 633; 344; 821; 114; 687; 238; 902; 717; 519; 280; 775; 893; 622; 187; 280; 723; 599; 31; 239; 250; 797; 888; 959; 161; 589; 20; 466; 465; 106; 806; 169; 618; 233; 436; 19; 11; 531; 969; 115; 116; 184; 122; 816; 243; 179; 594; 58; 661; 41; 580; 691; 821; 189; 706; 825; 521; 441; 521; 416; 297; 581; 466; 499; 663; 649; 59; 420; 51; 361; 669; 472; 514; 742; 9; 575; 5; 561; 916; 840; 421; 207; 578; 146; 213; 420; 486; 955; 584; 595; 673; 959; 169; 327; 547; 392; 904; 602; 848; 218; 280; 331; 878; 388; 510; 690; 228; 927; 700; 262; 384; 651; 774; 713; 448; 881; 285; 302; 980; 512; 980; 524; 2; 444; 879; 20; 656; 831; 553; 993; 171; 96; 368; 848; 269; 437; 188; 788; 590; 976; 874; 925; 921; 533; 673; 795; 536; 890; 813; 797; 90; 615; 845; 529; 848; 568; 75; 672; 841; 564; 684; 751; 538; 740; 180; 655; 762; 1; 755; 760; 376; 650; 210; 521; 982; 317; 920; 353; 640; 661; 685; 717; 833; 477; 120; 719; 909; 116; 545; 777; 320; 25; 92; 491; 546; 126; 450; 622; 366; 862; 830; 794; 450; 818; 913; 202; 518; 865; 120; 193; 145; 759; 886; 702; 859; 63; 870; 198; 599; 859; 352; 412; 529; 899; 813; 632; 566; 777; 658; 790; 43; 919; 958; 831; 975; 579; 39; 587; 952; 292; 892; 35; 203; 568; 555; 209; 937; 298; 899; 228; 167; 67; 893; 412; 4; 702; 383; 284; 284; 491; 925; 63; 455; 681; 544; 452; 55; 119; 819; 846; 305; 598; 586; 467; 546; 901; 925; 819; 416; 651; 96; 307; 774; 212; 550; 676; 904; 156; 117; 628; 612; 113; 914; 571; 230; 426; 826; 599; 535; 1000; 906; 659; 586; 224; 890; 738; 7; 609; 674; 712; 259; 683; 751; 123; 17; 822; 275; 570; 659; 69; 835; 939; 62; 408; 690; 979; 548; 99; 996; 782; 281; 774; 445; 847; 828; 286; 711; 559; 847; 564; 303; 588; 840; 770; 993; 889; 107; 626; 658; 798; 116; 93; 688; 115; 207; 82; 292; 787; 472; 441; 701; 596; 636; 100; 931; 945; 96; 522; 50; 209; 105; 82; 983; 945; 637; 462; 508; 353; 213; 474; 419; 374; 162; 416; 837; 58; 183; 272; 745; 979; 660; 289; 939; 552; 654; 721; 490; 891; 846; 222; 351; 697; 206; 876; 955; 493; 917; 767; 144; 902; 515; 396; 503; 631; 605; 596; 966; 265; 117; 164; 266; 494; 626; 46; 589; 865; 276; 521; 374; 790; 730; 34; 778; 138; 402; 455; 194; 690; 942; 486; 943; 224; 822; 145; 178; 665; 269; 226; 167; 143; 386; 130; 211; 986; 402; 506; 495; 122; 408; 556; 488; 636; 254; 374; 952; 133; 614; 367; 1000; 501; 153; 296; 604; 157; 742; 518; 865; 794; 950; 917; 542; 225; 457; 157; 637; 673; 991; 70; 507; 393; 552; 350; 340; 207; 797; 710; 144; 205; 251; 982; 852; 528; 615; 414; 937; 274; 619; 569; 198; 720; 910; 687; 742; 988; 980; 618; 684; 223; 385; 825; 354; 785; 732; 76; 784; 724; 293; 420; 304; 0; 748; 74; 140; 684; 689; 468; 504; 535; 704; 973; 596; 984; 93; 356; 319; 441; 300; 640; 197; 506; 243; 633; 436; 955; 935; 865; 944; 643; 40; 875; 112; 708; 585; 930; 260; 774; 164; 224; 231; 236; 856; 228; 58; 565; 400; 880; 375; 229; 77; 68; 932; 810; 456; 878; 269; 628; 79; 342; 913; 365; 802; 914; 9; 935; 723; 516; 775; 814; 811; 730; 809; 573; 788; 703; 740; 484; 904; 883; 384; 440; 283; 461; 691; 153; 959; 522; 82; 118; 569; 794; 341; 24; 996; 874; 787; 194; 825; 517; 25; 603; 480; 340; 906; 642; 99; 962; 94; 854; 339; 53; 533; 201; 539; 58; 477; 829; 653; 842; 205; 96; 825; 553; 636; 319; 7; 253; 602; 56; 19; 952; 790; 743; 253; 252; 724; 594; 851; 467; 830; 506; 590; 988; 276; 428; 916; 702; 638; 34; 630; 896; 510; 406; 440; 732; 234; 242; 188; 885; 657; 452; 811; 552; 180; 340; 681; 192; 851; 540; 451; 832; 942; 416; 390; 596; 358; 571; 199; 281; 463; 946; 967; 65; 463; 780; 289; 310; 414; 838; 931; 756; 523; 984; 561; 68; 756; 870; 937; 148; 136; 614; 194; 453; 852; 334; 957; 846; 689; 168; 108; 271; 159; 956; 344; 225; 110; 151; 954; 651; 465; 248; 270; 97; 853; 101; 508; 454; 819; 293; 731; 985; 927; 53; 803; 165; 552; 146; 653; 684; 312; 950; 981; 279; 161; 700; 825; 562; 134; 14; 750; 832; 60; 164; 488; 803; 110; 225; 88; 890; 498; 607; 223; 249; 659; 490; 730; 396; 858; 883; 123; 882; 480; 604; 940; 651; 45; 280; 55; 37; 233; 695; 32; 262; 312].

Definition lsum (xs : list int) : int := fold_left (fun a x => a + x) xs 0.

Fixpoint qs_loop (k : nat) (acc : int) : int :=
  match k with
  | O => acc + lsum (qs big unsorted) + lsum (qs big unsorted') + lsum (qs big unsorted'')
  | S k => qs_loop k (qs_loop k acc)
  end.

Definition quicksort_bench := qs_loop 12 0.

(** * derivative *)

Inductive expr := Add (l : list expr) | Sub (l : list expr) | Mul (l : list expr) | Div (l : list expr) | Num (n : int) | X.

Definition foldlEq {A B} (f : A -> B -> bool -> bool) (init : bool) (l1 : list A) (l2 : list B) : bool :=
  let fix foldf (xs : list A) (ys : list B) (accum : bool) :=
    match xs, ys with
    | x :: xs, y :: ys => foldf xs ys (f x y accum)
    | [], [] => accum
    | _, _ => false
    end in
  foldf l1 l2 init.

Fixpoint equal (f : nat) (a b : expr) : bool :=
  match f with
  | O => false
  | S f =>
      let chk (x y : expr) (acc : bool) := if acc then equal f x y else false in
      match a, b with
      | X, X => true
      | Num a, Num b => a =? b
      | Add xs, Add ys | Sub xs, Sub ys | Mul xs, Mul ys | Div xs, Div ys => foldlEq chk true xs ys
      | _, _ => false
      end
  end.

Fixpoint emap (g : expr -> expr) (l : list expr) : list expr := match l with [] => [] | x :: l => g x :: emap g l end.

Fixpoint deriv (f : nat) (a : expr) : expr :=
  match f with
  | O => X
  | S f =>
      match a with
      | X => Num 1
      | Num _ => Num 0
      | Add es => Add (emap (deriv f) es)
      | Sub es => Sub (emap (deriv f) es)
      | Mul es => Mul [a; Add (emap (fun x => Div [deriv f x; x]) es)]
      | Div [x; y] => Sub [Div [deriv f x; y]; Div [x; Mul [y; y; deriv f y]]]
      | _ => X
      end
  end.

Definition b2i (b : bool) : int := if b then 1 else 0.

Definition doit (_ : unit) : int :=
  let mkExp a b := Sub [Add [Mul [Num 3; X; X]; Mul [a; X; X]; Mul [b; X]; Num 5]; X] in
  let mkAns a b := Sub [Add [
        Mul [Mul [Num 3; X; X]; Add [Div [Num 0; Num 3]; Div [Num 1; X]; Div [Num 1; X]]];
        Mul [Mul [a; X; X]; Add [Div [Num 0; a]; Div [Num 1; X]; Div [Num 1; X]]];
        Mul [Mul [b; X]; Add [Div [Num 0; b]; Div [Num 1; X]]];
        Num 0]; Num 1] in
  let a := Num 5 in
  let b := Num 7 in
  let exp := mkExp a b in
  let ans := mkAns a b in
  b2i (equal big ans (deriv big ans)) + b2i (equal big ans (deriv big ans)) +
  b2i (equal big (Num 2) (Num 1)) + b2i (equal big X (Num 1)) + b2i (equal big (Add []) (Sub [])) +
  b2i (equal big ans (deriv big exp)).

Fixpoint deriv_loop (k : nat) (acc : int) : int :=
  match k with
  | O => acc + doit tt
  | S k => deriv_loop k (deriv_loop k acc)
  end.

Definition derivative_bench := deriv_loop 18 0.

(** * streams *)

Inductive step (A S : Type) := Yield (a : A) (s : S) | Skip (s : S) | Done.
Arguments Yield {A S}. Arguments Skip {A S}. Arguments Done {A S}.

Inductive pull (S A : Type) := Pull (s : S) (st : S -> step A S).
Arguments Pull {S A}.

Definition pfromList {A} (xs : list A) : pull (list A) A :=
  Pull xs (fun l => match l with [] => Done | x :: xs => Yield x xs end).

Definition pmap {S A B} (f : A -> B) (p : pull S A) : pull S B :=
  let '(Pull s st) := p in
  Pull s (fun s => match st s with Done => Done | Skip s' => Skip s' | Yield a s' => Yield (f a) s' end).

Definition ptake {S A} (p : pull S A) (n : int) : pull (S * int) A :=
  let '(Pull s st) := p in
  Pull (s, n) (fun '(s, n) =>
    if n =? 0 then Done
    else match st s with Done => Done | Skip s' => Skip (s', n) | Yield a s' => Yield a (s', n - 1) end).

Definition pfilter {S A} (p : A -> bool) (q : pull S A) : pull S A :=
  let '(Pull s st) := q in
  Pull s (fun s => match st s with Done => Done | Skip s' => Skip s' | Yield a s' => if p a then Yield a s' else Skip s' end).

Definition push (S A : Type) := (A -> (unit -> S) -> S) -> (unit -> S) -> S.

Definition ufromList {S A} (xs : list A) : push S A :=
  fun c n => let fix go l := match l with [] => n tt | x :: xs => c x (fun _ => go xs) end in go xs.

Definition uzipWith {S2 S3 A B C} (f : A -> B -> C) (k : push (S2 -> S3) A) (p : pull S2 B) : push S3 C :=
  let '(Pull seed st) := p in
  fun c n =>
    k (fun a hyp => fun s =>
         match st s with
         | Done => hyp tt s
         | Skip s' => hyp tt s'
         | Yield b s' => c (f a b) (fun _ => hyp tt s')
         end)
      (fun _ => fun _ => n tt)
      seed.

Definition ufoldl {A B} (f : A -> B -> B) (acc : B) (k : push B A) : B := k (fun a s => f a (s tt)) (fun _ => acc).

Definition complex (xs ys : list int) : list (int * int) :=
  let xs := pfromList xs in
  let xs := pmap (fun x => x * x) xs in
  let xs := ptake xs 12 in
  let xs := pfilter (fun n => PrimInt63.mod n 2 =? 0) xs in
  let xs := pmap (fun x => x * x) xs in
  let ys := ufromList ys in
  let s := uzipWith (fun a b => (a, b)) ys xs in
  ufoldl (fun a l => a :: l) [] s.

Definition s1 : list int := [1; 2; 3; 4; 5; 6].
Definition s2 : list int := [10; 20; 30; 40; 50; 60].

Fixpoint sumPairs (xs : list (int * int)) (acc : int) : int :=
  match xs with [] => acc | (a, b) :: r => sumPairs r (acc + a + b) end.

Fixpoint streams_loop (k : nat) (acc : int) : int :=
  match k with
  | O => sumPairs (complex s1 s2) acc
  | S k => streams_loop k (streams_loop k acc)
  end.

Definition streams_bench := streams_loop 23 0.

(** * interpreter *)

Fixpoint ilength {A} (xs : list A) (n : int) : int := match xs with [] => n | _ :: r => ilength r (n + 1) end.

Fixpoint foldr2 {A B C} (f : A -> B -> C -> C) (base : C) (l1 : list A) (l2 : list B) : C :=
  match l1, l2 with
  | a :: r1, b :: r2 => f a b (foldr2 f base r1 r2)
  | _, _ => base
  end.

Fixpoint ifoldl {A B} (f : A -> B -> B) (base : B) (l : list A) : B :=
  match l with [] => base | a :: r => ifoldl f (f a base) r end.

Inductive prim := Plus | Times | Assign | Ref | Deref.

Inductive iexp :=
| Int (i : int)
| Var (x : int)
| Fun (xs : list int) (body : iexp)
| Call (f : iexp) (args : list iexp)
| IfZero (a b c : iexp)
| Letrec (binds : list (int * (list int * iexp))) (body : iexp)
| Prim (p : prim).

Inductive value := VInt (i : int) | VClo (lam : list int * iexp) (env : list (int * int)) | VPrim (p : prim) | VCell (a : int).

Definition extend {A} (map : list (int * A)) (a : int) (b : A) : list (int * A) := (a, b) :: map.

Fixpoint find_env (map : list (int * int)) (a b : int) : int :=
  match map with [] => b | (a', b') :: rst => if a =? a' then b' else find_env rst a b end.

Fixpoint find_store (map : list (int * value)) (a : int) (b : value) : value :=
  match map with [] => b | (a', b') :: rst => if a =? a' then b' else find_store rst a b end.

Definition interpret (e0 : iexp) : value :=
  let dummy_address := 0 in
  let dummy_value := VInt 0 in
  let lookup_env env x := find_env env x dummy_address in
  let lookup_store store a := find_store store a dummy_value in
  let dummy (store : list (int * value)) (n : int) := (dummy_value, store, n) in
  let makePrim p vs store n :=
    match p, vs with
    | Plus, [VInt i1; VInt i2] => (VInt (i1 + i2), store, n)
    | Times, [VInt i1; VInt i2] => (VInt (i1 * i2), store, n)
    | Ref, [v] => (VCell n, extend store n v, n + 1)
    | Deref, [VCell n'] => (lookup_store store n', store, n)
    | Assign, [VCell n'; v] => (lookup_store store n', extend store n' v, n)
    | _, _ => dummy store n
    end in
  let fix aux (f : nat) (e : iexp) (env : list (int * int)) (store : list (int * value)) (n : int)
      : value * list (int * value) * int :=
    match f with
    | O => dummy store n
    | S f =>
        match e with
        | Int i => (VInt i, store, n)
        | Var x => (lookup_store store (lookup_env env x), store, n)
        | Fun xs body => (VClo (xs, body) env, store, n)
        | Call fe args =>
            let '(f', store, n) := aux f fe env store n in
            let '(args_rev', store, n) :=
              ifoldl (fun arg '(args', store, n) =>
                        let '(arg', store, n) := aux f arg env store n in (arg' :: args', store, n))
                     ([], store, n) args in
            let args' := rev args_rev' in
            match f' with
            | VClo (params, body) env =>
                if ilength args_rev' 0 =? ilength params 0 then
                  let '(env, store, n) :=
                    foldr2 (fun a b '(env, store, n) => (extend env a n, extend store n b, n + 1))
                           (env, store, n) params args' in
                  aux f body env store n
                else dummy store n
            | VPrim p => makePrim p args' store n
            | _ => dummy store n
            end
        | IfZero tst thn els =>
            let '(tst', store, n) := aux f tst env store n in
            match tst' with
            | VInt i => if i =? 0 then aux f thn env store n else aux f els env store n
            | _ => aux f els env store n
            end
        | Letrec binds body =>
            let '(n', env) := ifoldl (fun '(x, lam) '(n, env) => (n + 1, extend env x n)) (n, env) binds in
            let store := ifoldl (fun '(x, lam) store => extend store (lookup_env env x) (VClo lam env)) store binds in
            aux f body env store n'
        | Prim p => (VPrim p, store, n)
        end
    end in
  let '(final, _, _) := aux big e0 [] [(dummy_address, dummy_value)] (dummy_address + 1) in
  final.

Definition m1 : int := 0 - 1.

Definition prog6 :=
  Letrec [(1, ([2], Letrec [(3, ([4], IfZero (Var 4) (Var 2) (Int m1)))] (Var 3)))]
         (Call (Call (Var 1) [Int 1]) [Int 10]).

Definition prim_ref := Fun [1; 2] (Call (Var 1) [Call (Prim Ref) [Var 2]]).
Definition prim_deref := Fun [1; 2] (Call (Var 1) [Call (Prim Deref) [Var 2]]).
Definition prim_assign := Fun [1; 2; 3] (Call (Var 1) [Call (Prim Assign) [Var 2; Var 3]]).

Definition prog7 :=
  Call (Fun [101]
          (Call prim_ref
             [Fun [1]
                (Call (Fun [102; 0]
                         (Call (Fun [104]
                                  (Call (Fun [7]
                                           (Call prim_deref
                                              [Fun [6] (IfZero (Var 6)
                                                               (Call (Var 104) [Int 0])
                                                               (Call (Var 104) [Var 7]));
                                               Var 0]))
                                        [Fun [105; 8] (Call (Var 104) [Var 8])]))
                               [Fun [5]
                                  (Call prim_assign
                                     [Fun [2]
                                        (Call (Fun [103; m1]
                                                 (Call prim_deref
                                                    [Fun [3]
                                                       (IfZero (Var 3)
                                                               (Call (Var 103) [Int 42])
                                                               (Call prim_deref
                                                                  [Fun [4] (Call (Var 4) [Var 103; Int 0]);
                                                                   Var 0]));
                                                     Var 0]))
                                              [Var 102; Var 2]);
                                      Var 0;
                                      Var 5])]))
                      [Var 101; Var 1]);
              Fun [100; 0] (Call (Var 100) [Var 0])]))
       [Fun [1] (Var 1)].

Definition prog8 := IfZero (Int 0) (Int 1) (Int 2).

Definition vint (v : value) : int := match v with VInt i => i | _ => 0 end.

Fixpoint interp_loop (k : nat) (acc : int) : int :=
  match k with
  | O => acc + vint (interpret prog6) + vint (interpret prog7) + vint (interpret prog8)
  | S k => interp_loop k (interp_loop k acc)
  end.

Definition interpreter_bench := interp_loop 18 0.


CertiRocq Compile -O 1 -ext "_base" ack_bench.
CertiRocq Compile -O 2 -ext "_web" ack_bench.

CertiRocq Compile -O 1 -ext "_base" tak_bench.
CertiRocq Compile -O 2 -ext "_web" tak_bench.

CertiRocq Compile -O 1 -ext "_base" cpstak_bench.
CertiRocq Compile -O 2 -ext "_web" cpstak_bench.

CertiRocq Compile -O 1 -ext "_base" yfact_bench.
CertiRocq Compile -O 2 -ext "_web" yfact_bench.

CertiRocq Compile -O 1 -ext "_base" nqueens_bench.
CertiRocq Compile -O 2 -ext "_web" nqueens_bench.

CertiRocq Compile -O 1 -ext "_base" filter_bench.
CertiRocq Compile -O 2 -ext "_web" filter_bench.

CertiRocq Compile -O 1 -ext "_base" quicksort_bench.
CertiRocq Compile -O 2 -ext "_web" quicksort_bench.

CertiRocq Compile -O 1 -ext "_base" derivative_bench.
CertiRocq Compile -O 2 -ext "_web" derivative_bench.

CertiRocq Compile -O 1 -ext "_base" streams_bench.
CertiRocq Compile -O 2 -ext "_web" streams_bench.

CertiRocq Compile -O 1 -ext "_base" interpreter_bench.
CertiRocq Compile -O 2 -ext "_web" interpreter_bench.
