Definition Sk2_cf0_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(- rat_of_Z 1 * (n + rat_of_Z 2 + k) * (- n + k + rat_of_Z 1) * (n + rat_of_Z 1 + k)^2 * (- n + k)^2) / (((k + rat_of_Z 1) * (k + rat_of_Z 2)^5)).

Definition Sk2_cf0_1 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
((n + rat_of_Z 2 + k) * (- n + k + rat_of_Z 1) * (rat_of_Z 2 * k^3 + rat_of_Z 8 * k^2 + rat_of_Z 11 * k + rat_of_Z 5 + - k * n + - k * n^2 + - rat_of_Z 2 * n^2 + - rat_of_Z 2 * n)) / ((k + rat_of_Z 2)^5).

Definition Sk2 (v : int -> int -> rat) := forall (n_ k_ : int), precond.Sk2 n_ k_ ->
v n_ (int.shift 2 k_) = Sk2_cf0_0 n_ k_ * v n_ k_ + Sk2_cf0_1 n_ k_ * v n_ (int.shift 1 k_).

Definition SnSk_cf0_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
((n + rat_of_Z 2 + k) * (- n + k) * (n + rat_of_Z 1 + k)^2) / ((k + rat_of_Z 1)^4).

Definition SnSk_cf1_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
((n + rat_of_Z 2 + k)^2 * (- n + - rat_of_Z 1 + k)^2) / ((k + rat_of_Z 1)^4).

Definition SnSk_cf0_1 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(- n + - rat_of_Z 2 + - k) / ((- n + k)).

Definition SnSk (v : int -> int -> rat) := forall (n_ k_ : int), precond.SnSk n_ k_ ->
v (int.shift 1 n_) (int.shift 1 k_) = SnSk_cf0_0 n_ k_ * v n_ k_ + SnSk_cf1_0 n_ k_ * v (int.shift 1 n_) k_ + SnSk_cf0_1 n_ k_ * v n_ (int.shift 1 k_).

Definition Sn2_cf0_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(- rat_of_Z 1 * (n + rat_of_Z 2 + k) * (rat_of_Z 2 + rat_of_Z 9 * n^2 + - rat_of_Z 3 * k * n + rat_of_Z 6 * k^2 + n^4 + rat_of_Z 5 * n^3 + rat_of_Z 6 * k^3 + k * n^3 + - k * n^2 + - rat_of_Z 4 * k^2 * n^2 + - rat_of_Z 2 * k^2 * n + rat_of_Z 4 * k^3 * n + k + rat_of_Z 7 * n) * (n + rat_of_Z 1 + k)^2) / (((n + rat_of_Z 2)^3 * (- n + - rat_of_Z 1 + k)^2 * (k + - n + - rat_of_Z 2)^2)).

Definition Sn2_cf1_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
((rat_of_Z 2 * n + rat_of_Z 3) * (n^2 + rat_of_Z 3 * n + rat_of_Z 3) * (n + rat_of_Z 2 + k)^2) / (((n + rat_of_Z 2)^3 * (k + - n + - rat_of_Z 2)^2)).

Definition Sn2_cf0_1 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(rat_of_Z 2 * k * (rat_of_Z 2 * n + rat_of_Z 3) * (k + rat_of_Z 1)^5 * (n + rat_of_Z 2 + k)) / (((n + rat_of_Z 2)^3 * (- n + k) * (- n + - rat_of_Z 1 + k)^2 * (k + - n + - rat_of_Z 2)^2)).

Definition Sn2 (v : int -> int -> rat) := forall (n_ k_ : int), precond.Sn2 n_ k_ ->
v (int.shift 2 n_) k_ = Sn2_cf0_0 n_ k_ * v n_ k_ + Sn2_cf1_0 n_ k_ * v (int.shift 1 n_) k_ + Sn2_cf0_1 n_ k_ * v n_ (int.shift 1 k_).

Definition P_cf0 (n_ : int) : rat :=
let n : rat := n_%:~R in
((rat_of_Z 2 * n + rat_of_Z 7) * (rat_of_Z 928 + rat_of_Z 1266 * n + rat_of_Z 643 * n^2 + rat_of_Z 144 * n^3 + rat_of_Z 12 * n^4) * (n + rat_of_Z 1)^6).

Definition P_cf1 (n_ : int) : rat :=
let n : rat := n_%:~R in
(- rat_of_Z 1 * (rat_of_Z 2 * n + rat_of_Z 3) * (rat_of_Z 2 * n + rat_of_Z 7) * (rat_of_Z 408 * n^9 + rat_of_Z 7956 * n^8 + rat_of_Z 68086 * n^7 + rat_of_Z 336284 * n^6 + rat_of_Z 1058890 * n^5 + rat_of_Z 2209767 * n^4 + rat_of_Z 3063206 * n^3 + rat_of_Z 2724789 * n^2 + rat_of_Z 1413006 * n + rat_of_Z 325664)).

Definition P_cf2 (n_ : int) : rat :=
let n : rat := n_%:~R in
((rat_of_Z 2 * n + rat_of_Z 5) * (rat_of_Z 13896 * n^10 + rat_of_Z 347400 * n^9 + rat_of_Z 3868998 * n^8 + rat_of_Z 25269960 * n^7 + rat_of_Z 107159724 * n^6 + rat_of_Z 308199360 * n^5 + rat_of_Z 608681313 * n^4 + rat_of_Z 814935630 * n^3 + rat_of_Z 707785777 * n^2 + rat_of_Z 360083510 * n + rat_of_Z 81495208)).

Definition P_cf3 (n_ : int) : rat :=
let n : rat := n_%:~R in
(- rat_of_Z 1 * (rat_of_Z 2 * n + rat_of_Z 3) * (rat_of_Z 2 * n + rat_of_Z 7) * (rat_of_Z 408 * n^9 + rat_of_Z 10404 * n^8 + rat_of_Z 117046 * n^7 + rat_of_Z 761526 * n^6 + rat_of_Z 3153520 * n^5 + rat_of_Z 8607233 * n^4 + rat_of_Z 15461616 * n^3 + rat_of_Z 17602001 * n^2 + rat_of_Z 11509566 * n + rat_of_Z 3291016)).

Definition P_cf4 (n_ : int) : rat :=
let n : rat := n_%:~R in
((rat_of_Z 2 * n + rat_of_Z 3) * (rat_of_Z 12 * n^4 + rat_of_Z 96 * n^3 + rat_of_Z 283 * n^2 + rat_of_Z 364 * n + rat_of_Z 173) * (n + rat_of_Z 4)^6).

Definition P_flat (v : int -> rat) (n_ : int) : rat :=
P_cf0 n_ * v n_ + P_cf1 n_ * v (int.shift 1 n_) + P_cf2 n_ * v (int.shift 2 n_) + P_cf3 n_ * v (int.shift 3 n_) + P_cf4 n_ * v (int.shift 4 n_).

Definition P_seq := [:: P_cf0; P_cf1; P_cf2; P_cf3; P_cf4].

Definition P_horner := punk.horner_seqop P_seq.

Definition Q_cf0_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(rat_of_Z 4 * k * (rat_of_Z 2 * n + rat_of_Z 5) * (rat_of_Z 2 * n + rat_of_Z 3) * (rat_of_Z 2 * n + rat_of_Z 7) * (rat_of_Z 1744402215 * k^2 * n^14 + - rat_of_Z 390926048 * k * n^15 + - rat_of_Z 1797543582 * k * n^14 + - rat_of_Z 27184619520 * n^2 + rat_of_Z 25107052032 * k * n + rat_of_Z 2077567488 * k^2 + - rat_of_Z 332796611328 * n^4 + - rat_of_Z 120646983168 * n^3 + - rat_of_Z 6189000960 * k^3 + - rat_of_Z 3452904576 * k^4 + rat_of_Z 258088741728 * k * n^3 + rat_of_Z 102524693760 * k * n^2 + rat_of_Z 121546930272 * k^2 * n^2 + rat_of_Z 23906184192 * k^2 * n + - rat_of_Z 47918897056 * k^3 * n + - rat_of_Z 453776761464 * k^4 * n^6 + - rat_of_Z 34208713762 * k^6 * n^4 + - rat_of_Z 29608827881 * k^6 * n^3 + rat_of_Z 5592448786 * k^8 * n + rat_of_Z 14155092397 * k^8 * n^2 + - rat_of_Z 616679187165 * k^3 * n^7 + rat_of_Z 2863226880 * k + - rat_of_Z 2863226880 * n + - rat_of_Z 673265061944 * k^3 * n^4 + - rat_of_Z 30134039386 * k^7 * n^2 + - rat_of_Z 328103820800 * n^10 + - rat_of_Z 859845193968 * n^8 + - rat_of_Z 591626761600 * n^9 + - rat_of_Z 998105211488 * n^7 + - rat_of_Z 10833443724 * k^7 * n + - rat_of_Z 911577929600 * n^6 + - rat_of_Z 639897370880 * n^5 + rat_of_Z 255690672 * k^9 + - rat_of_Z 409497350480 * k^3 * n^3 + - rat_of_Z 176289543184 * k^3 * n^2 + rat_of_Z 445980429568 * k * n^4 + rat_of_Z 779418105800 * k^2 * n^4 + rat_of_Z 372081953600 * k^2 * n^3 + - rat_of_Z 27857118128 * k^4 * n + rat_of_Z 555594416928 * k * n^5 + - rat_of_Z 405743014925 * k^4 * n^4 + - rat_of_Z 247666013854 * k^4 * n^3 + rat_of_Z 182888462394 * k^5 * n^3 + rat_of_Z 81436213660 * k^5 * n^2 + - rat_of_Z 18444006265 * k^6 * n^2 + - rat_of_Z 7247159210 * k^6 * n + - rat_of_Z 105299641272 * k^4 * n^2 + rat_of_Z 22679880432 * k^5 * n + - rat_of_Z 1333959512 * k^6 + - rat_of_Z 1822888416 * k^7 + rat_of_Z 1023021688 * k^8 + rat_of_Z 2997847184 * k^5 + rat_of_Z 63848152 * k^11 * n + - rat_of_Z 1719699936 * k^10 * n^3 + rat_of_Z 139771620 * k^11 * n^3 + rat_of_Z 123447892 * k^11 * n^2 + rat_of_Z 102640379 * k^11 * n^4 + rat_of_Z 17466166 * k^11 * n^6 + rat_of_Z 51093252 * k^11 * n^5 + - rat_of_Z 87428804 * k^10 * n^7 + - rat_of_Z 311211346 * k^10 * n^6 + - rat_of_Z 783589496 * k^10 * n^5 + - rat_of_Z 1394901560 * k^10 * n^4 + - rat_of_Z 674057028 * k^10 * n + - rat_of_Z 1397856374 * k^10 * n^2 + rat_of_Z 2124 * k^11 * n^10 + - rat_of_Z 5808 * k^10 * n^11 + - rat_of_Z 900 * k^9 * n^12 + rat_of_Z 14016 * k^8 * n^13 + - rat_of_Z 9660 * k^7 * n^14 + - rat_of_Z 7440 * k^6 * n^15 + rat_of_Z 13044 * k^5 * n^16 + - rat_of_Z 3456 * k^4 * n^17 + - rat_of_Z 3648 * k^3 * n^18 + rat_of_Z 3072 * k^2 * n^19 + rat_of_Z 53916 * k^11 * n^9 + - rat_of_Z 168060 * k^10 * n^10 + - rat_of_Z 7968 * k^9 * n^11 + rat_of_Z 439032 * k^8 * n^12 + - rat_of_Z 342996 * k^7 * n^13 + - rat_of_Z 234732 * k^6 * n^14 + rat_of_Z 482568 * k^5 * n^15 + - rat_of_Z 147696 * k^4 * n^16 + - rat_of_Z 144048 * k^3 * n^17 + rat_of_Z 128928 * k^2 * n^18 + - rat_of_Z 32256 * k * n^19 + rat_of_Z 610071 * k^11 * n^8 + - rat_of_Z 2193376 * k^10 * n^9 + rat_of_Z 154863 * k^9 * n^10 + rat_of_Z 6305692 * k^8 * n^11 + - rat_of_Z 5568967 * k^7 * n^12 + - rat_of_Z 3398600 * k^6 * n^13 + rat_of_Z 8280997 * k^5 * n^14 + - rat_of_Z 2912340 * k^4 * n^15 + - rat_of_Z 2673124 * k^3 * n^16 + rat_of_Z 2543776 * k^2 * n^17 + - rat_of_Z 631552 * k * n^18 + rat_of_Z 4050412 * k^11 * n^7 + - rat_of_Z 17034532 * k^10 * n^8 + rat_of_Z 3467507 * k^9 * n^9 + rat_of_Z 55016357 * k^8 * n^10 + - rat_of_Z 54855522 * k^7 * n^11 + - rat_of_Z 29964918 * k^6 * n^12 + rat_of_Z 87494875 * k^5 * n^13 + - rat_of_Z 35252851 * k^4 * n^14 + - rat_of_Z 31003896 * k^3 * n^15 + rat_of_Z 31367368 * k^2 * n^16 + - rat_of_Z 7645312 * k * n^17 + - rat_of_Z 252131679 * k^3 * n^14 + rat_of_Z 271060288 * k^2 * n^15 + - rat_of_Z 63952392 * k * n^16 + - rat_of_Z 3685794720 * n^14 + - rat_of_Z 681771968 * n^15 + - rat_of_Z 97183888 * n^16 + - rat_of_Z 10296800 * n^17 + - rat_of_Z 768 * n^20 + - rat_of_Z 35328 * n^19 + - rat_of_Z 763360 * n^18 + rat_of_Z 325582047 * k^8 * n^9 + - rat_of_Z 366581765 * k^7 * n^10 + - rat_of_Z 180195424 * k^6 * n^11 + rat_of_Z 637095193 * k^5 * n^12 + - rat_of_Z 293786083 * k^4 * n^13 + rat_of_Z 1381460896 * k^8 * n^8 + - rat_of_Z 1759973356 * k^7 * n^9 + - rat_of_Z 785707110 * k^6 * n^10 + rat_of_Z 3390299217 * k^5 * n^11 + - rat_of_Z 1790786379 * k^4 * n^12 + - rat_of_Z 1528641105 * k^3 * n^13 + rat_of_Z 4329005311 * k^8 * n^7 + - rat_of_Z 6267925410 * k^7 * n^8 + - rat_of_Z 2584329138 * k^6 * n^9 + rat_of_Z 13641244822 * k^5 * n^10 + - rat_of_Z 8275822234 * k^4 * n^11 + - rat_of_Z 7171164950 * k^3 * n^12 + rat_of_Z 8671244945 * k^2 * n^13 + rat_of_Z 10157899122 * k^8 * n^6 + - rat_of_Z 16846739030 * k^7 * n^7 + - rat_of_Z 6608736882 * k^6 * n^8 + rat_of_Z 42343375448 * k^5 * n^9 + - rat_of_Z 29644875275 * k^4 * n^10 + - rat_of_Z 26657515127 * k^3 * n^11 + rat_of_Z 34074345499 * k^2 * n^12 + - rat_of_Z 6281404994 * k * n^13 + rat_of_Z 17873852947 * k^8 * n^5 + - rat_of_Z 34403563419 * k^7 * n^6 + - rat_of_Z 13486898969 * k^6 * n^7 + rat_of_Z 102510705804 * k^5 * n^8 + - rat_of_Z 83411422057 * k^4 * n^9 + - rat_of_Z 79729894768 * k^3 * n^10 + rat_of_Z 107414839637 * k^2 * n^11 + - rat_of_Z 16511136494 * k * n^12 + rat_of_Z 23326085212 * k^8 * n^4 + - rat_of_Z 53241708152 * k^7 * n^5 + - rat_of_Z 22441935459 * k^6 * n^6 + rat_of_Z 194292424443 * k^5 * n^7 + - rat_of_Z 185590186906 * k^4 * n^8 + - rat_of_Z 193594433821 * k^3 * n^9 + rat_of_Z 273992904577 * k^2 * n^10 + - rat_of_Z 31057152218 * k * n^11 + - rat_of_Z 383034928990 * k^3 * n^8 + rat_of_Z 567647259943 * k^2 * n^9 + - rat_of_Z 34242238930 * k * n^10 + - rat_of_Z 15710071840 * n^13 + - rat_of_Z 147311006048 * n^11 + - rat_of_Z 53560818048 * n^12 + - rat_of_Z 146056688 * k^10 + rat_of_Z 954502237105 * k^2 * n^8 + rat_of_Z 9342208346 * k * n^9 + - rat_of_Z 768 * k * n^20 + rat_of_Z 134837704206 * k * n^8 + - rat_of_Z 490926362370 * k^4 * n^5 + rat_of_Z 286016170951 * k^5 * n^4 + rat_of_Z 506405609304 * k * n^6 + rat_of_Z 1197029877604 * k^2 * n^5 + - rat_of_Z 802371636049 * k^3 * n^6 + - rat_of_Z 832398382758 * k^3 * n^5 + rat_of_Z 329600901794 * k * n^7 + rat_of_Z 1295827185263 * k^2 * n^7 + rat_of_Z 1405464163068 * k^2 * n^6 + rat_of_Z 1211927256 * k^9 * n + rat_of_Z 3251918342 * k^9 * n^3 + rat_of_Z 2579633352 * k^9 * n^2 + rat_of_Z 2693929255 * k^9 * n^4 + rat_of_Z 31316929 * k^9 * n^8 + rat_of_Z 169665992 * k^9 * n^7 + rat_of_Z 612974365 * k^9 * n^6 + rat_of_Z 1536374559 * k^9 * n^5 + rat_of_Z 14685520 * k^11 + - rat_of_Z 61627367257 * k^7 * n^4 + - rat_of_Z 326900137446 * k^4 * n^7 + - rat_of_Z 51889742508 * k^7 * n^3 + rat_of_Z 329102354583 * k^5 * n^5 + rat_of_Z 21970944881 * k^8 * n^3 + rat_of_Z 287538055025 * k^5 * n^6 + - rat_of_Z 30741445978 * k^6 * n^5)) / (((- n + - rat_of_Z 1 + k)^2 * (- n + - rat_of_Z 4 + k)^2 * (n + rat_of_Z 3)^3 * (n + rat_of_Z 2)^3 * (k + - n + - rat_of_Z 3)^2 * (- n + - rat_of_Z 2 + k)^2)).

Definition Q_cf1_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(- rat_of_Z 4 * (rat_of_Z 2 * n + rat_of_Z 5) * (rat_of_Z 2 * n + rat_of_Z 3) * (rat_of_Z 2 * n + rat_of_Z 7) * (- rat_of_Z 768 * k^2 * n^14 + rat_of_Z 3456 * k * n^15 + rat_of_Z 128352 * k * n^14 + - rat_of_Z 67908067008 * n^2 + rat_of_Z 9099997808 * k * n + rat_of_Z 310664672 * k^2 + - rat_of_Z 175893838000 * n^4 + - rat_of_Z 131207942960 * n^3 + - rat_of_Z 169882072 * k^3 + rat_of_Z 16459280 * k^4 + rat_of_Z 52615736598 * k * n^3 + rat_of_Z 27869086208 * k * n^2 + rat_of_Z 4186382212 * k^2 * n^2 + rat_of_Z 1686931392 * k^2 * n + - rat_of_Z 944024994 * k^3 * n + rat_of_Z 114305270 * k^4 * n^6 + - rat_of_Z 693288259 * k^3 * n^7 + rat_of_Z 1381092384 * k + - rat_of_Z 21794233216 * n + - rat_of_Z 3964985038 * k^3 * n^4 + - rat_of_Z 3448870336 * n^10 + - rat_of_Z 34419976280 * n^8 + - rat_of_Z 12314690524 * n^9 + - rat_of_Z 75583675964 * n^7 + - rat_of_Z 130014624048 * n^6 + - rat_of_Z 173414173068 * n^5 + - rat_of_Z 3754252403 * k^3 * n^3 + - rat_of_Z 2412870465 * k^3 * n^2 + rat_of_Z 68467857071 * k * n^4 + rat_of_Z 6286099260 * k^2 * n^4 + rat_of_Z 6267688586 * k^2 * n^3 + rat_of_Z 88023212 * k^4 * n + rat_of_Z 65027372713 * k * n^5 + rat_of_Z 316850268 * k^4 * n^4 + rat_of_Z 318395514 * k^4 * n^3 + rat_of_Z 215308166 * k^4 * n^2 + - rat_of_Z 1240448 * n^14 + - rat_of_Z 63984 * n^15 + - rat_of_Z 1536 * n^16 + rat_of_Z 768 * k^4 * n^12 + - rat_of_Z 1728 * k^3 * n^13 + rat_of_Z 21912 * k^4 * n^11 + - rat_of_Z 57072 * k^3 * n^12 + - rat_of_Z 20472 * k^2 * n^13 + rat_of_Z 284200 * k^4 * n^10 + - rat_of_Z 861540 * k^3 * n^11 + - rat_of_Z 229168 * k^2 * n^12 + rat_of_Z 2207580 * k * n^13 + rat_of_Z 2216476 * k^4 * n^9 + - rat_of_Z 7872580 * k^3 * n^10 + - rat_of_Z 1284268 * k^2 * n^11 + rat_of_Z 23327476 * k * n^12 + rat_of_Z 11581872 * k^4 * n^8 + - rat_of_Z 48600970 * k^3 * n^9 + - rat_of_Z 2229148 * k^2 * n^10 + rat_of_Z 169390270 * k * n^11 + - rat_of_Z 214150124 * k^3 * n^8 + rat_of_Z 19636326 * k^2 * n^9 + rat_of_Z 895491960 * k * n^10 + - rat_of_Z 14858072 * n^13 + - rat_of_Z 747916132 * n^11 + - rat_of_Z 123087048 * n^12 + rat_of_Z 178983116 * k^2 * n^8 + rat_of_Z 3561379481 * k * n^9 + rat_of_Z 10853226951 * k * n^8 + rat_of_Z 223378412 * k^4 * n^5 + rat_of_Z 46548168958 * k * n^6 + rat_of_Z 4425270962 * k^2 * n^5 + - rat_of_Z 1670758425 * k^3 * n^6 + - rat_of_Z 2999441626 * k^3 * n^5 + rat_of_Z 25562116926 * k * n^7 + rat_of_Z 780005826 * k^2 * n^7 + rat_of_Z 2218767840 * k^2 * n^6 + - rat_of_Z 3268333056 + rat_of_Z 42741626 * k^4 * n^7) * k^4) / (((- n + - rat_of_Z 2 + k)^2 * (- n + - rat_of_Z 4 + k)^2 * (n + rat_of_Z 2)^3 * (n + rat_of_Z 3)^3 * (k + - n + - rat_of_Z 3)^2)).

Definition Q_cf0_1 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(- rat_of_Z 4 * k * (rat_of_Z 2 * n + rat_of_Z 5) * (rat_of_Z 2 * n + rat_of_Z 3) * (rat_of_Z 2 * n + rat_of_Z 7) * (k + rat_of_Z 1)^5 * (rat_of_Z 285984 * k^2 * n^14 + - rat_of_Z 157920 * k * n^15 + - rat_of_Z 3026048 * k * n^14 + rat_of_Z 74867424768 * n^2 + - rat_of_Z 44680889088 * k * n + rat_of_Z 5162764032 * k^2 + rat_of_Z 241822754048 * n^4 + rat_of_Z 161603596032 * n^3 + - rat_of_Z 1744849824 * k^3 + - rat_of_Z 744986544 * k^4 + - rat_of_Z 281708015936 * k * n^3 + - rat_of_Z 142716403296 * k * n^2 + rat_of_Z 96887337056 * k^2 * n^2 + rat_of_Z 32825580096 * k^2 * n + - rat_of_Z 10344114032 * k^3 * n + - rat_of_Z 3469900135 * k^4 * n^6 + - rat_of_Z 1842594317 * k^6 * n^4 + - rat_of_Z 2262462688 * k^6 * n^3 + - rat_of_Z 13217484828 * k^3 * n^7 + - rat_of_Z 6512113152 * k + rat_of_Z 21458165760 * n + - rat_of_Z 54560718080 * k^3 * n^4 + rat_of_Z 123447892 * k^7 * n^2 + rat_of_Z 10042207744 * n^10 + rat_of_Z 75468444096 * n^8 + rat_of_Z 30900177104 * n^9 + rat_of_Z 146266755504 * n^7 + rat_of_Z 63848152 * k^7 * n + rat_of_Z 223624806496 * n^6 + rat_of_Z 266328825472 * n^5 + - rat_of_Z 47534432700 * k^3 * n^3 + - rat_of_Z 28334986440 * k^3 * n^2 + - rat_of_Z 384634123200 * k * n^4 + rat_of_Z 220377639732 * k^2 * n^4 + rat_of_Z 176090065112 * k^2 * n^3 + - rat_of_Z 3766672224 * k^4 * n + - rat_of_Z 385205224120 * k * n^5 + - rat_of_Z 11108830969 * k^4 * n^4 + - rat_of_Z 11977447248 * k^4 * n^3 + rat_of_Z 11326819614 * k^5 * n^3 + rat_of_Z 8499441560 * k^5 * n^2 + - rat_of_Z 1832048202 * k^6 * n^2 + - rat_of_Z 880287004 * k^6 * n + - rat_of_Z 8659675144 * k^4 * n^2 + rat_of_Z 3824239688 * k^5 * n + - rat_of_Z 190113248 * k^6 + rat_of_Z 14685520 * k^7 + rat_of_Z 780109264 * k^5 + - rat_of_Z 6720 * k^3 * n^14 + rat_of_Z 7488 * k^2 * n^15 + - rat_of_Z 3840 * k * n^16 + rat_of_Z 8872992 * n^14 + rat_of_Z 695008 * n^15 + rat_of_Z 33792 * n^16 + rat_of_Z 768 * n^17 + rat_of_Z 2124 * k^7 * n^10 + - rat_of_Z 7932 * k^6 * n^11 + rat_of_Z 8772 * k^5 * n^12 + - rat_of_Z 372 * k^4 * n^13 + rat_of_Z 53916 * k^7 * n^9 + - rat_of_Z 228348 * k^6 * n^10 + rat_of_Z 285576 * k^5 * n^11 + - rat_of_Z 24444 * k^4 * n^12 + - rat_of_Z 236508 * k^3 * n^13 + rat_of_Z 610071 * k^7 * n^8 + - rat_of_Z 2965195 * k^6 * n^9 + rat_of_Z 4228061 * k^5 * n^10 + - rat_of_Z 563929 * k^4 * n^11 + - rat_of_Z 3845816 * k^3 * n^12 + rat_of_Z 5069472 * k^2 * n^13 + rat_of_Z 4050412 * k^7 * n^7 + - rat_of_Z 22915157 * k^6 * n^8 + rat_of_Z 37634766 * k^5 * n^9 + - rat_of_Z 7062201 * k^4 * n^10 + - rat_of_Z 38297128 * k^3 * n^11 + rat_of_Z 55326472 * k^2 * n^12 + - rat_of_Z 35860680 * k * n^13 + rat_of_Z 17466166 * k^7 * n^6 + - rat_of_Z 117046206 * k^6 * n^7 + rat_of_Z 224250307 * k^5 * n^8 + - rat_of_Z 56308591 * k^4 * n^9 + - rat_of_Z 260924075 * k^3 * n^10 + rat_of_Z 415735739 * k^2 * n^11 + - rat_of_Z 294146400 * k * n^12 + rat_of_Z 51093252 * k^7 * n^5 + - rat_of_Z 414703096 * k^6 * n^6 + rat_of_Z 942042570 * k^5 * n^7 + - rat_of_Z 308693091 * k^4 * n^8 + - rat_of_Z 1286667926 * k^3 * n^9 + rat_of_Z 2278300097 * k^2 * n^10 + - rat_of_Z 1770637850 * k * n^11 + - rat_of_Z 4735827930 * k^3 * n^8 + rat_of_Z 9406632852 * k^2 * n^9 + - rat_of_Z 8090727306 * k * n^10 + rat_of_Z 78742896 * n^13 + rat_of_Z 2576225456 * n^11 + rat_of_Z 515413184 * n^12 + rat_of_Z 29795852850 * k^2 * n^8 + - rat_of_Z 28624383652 * k * n^9 + - rat_of_Z 79238310868 * k * n^8 + - rat_of_Z 7286006265 * k^4 * n^5 + rat_of_Z 10083400273 * k^5 * n^4 + - rat_of_Z 292723611810 * k * n^6 + rat_of_Z 201162981114 * k^2 * n^5 + - rat_of_Z 28108959555 * k^3 * n^6 + - rat_of_Z 45328273270 * k^3 * n^5 + - rat_of_Z 172186812834 * k * n^7 + rat_of_Z 73002514895 * k^2 * n^7 + rat_of_Z 138352054849 * k^2 * n^6 + rat_of_Z 102640379 * k^7 * n^4 + - rat_of_Z 1211427691 * k^4 * n^7 + rat_of_Z 139771620 * k^7 * n^3 + rat_of_Z 6319292362 * k^5 * n^5 + rat_of_Z 2859841811 * k^5 * n^6 + - rat_of_Z 1039509631 * k^6 * n^5 + rat_of_Z 2863226880)) / (((- n + k) * (k + - n + - rat_of_Z 3)^2 * (- n + - rat_of_Z 4 + k)^2 * (- n + - rat_of_Z 1 + k)^2 * (n + rat_of_Z 3)^3 * (n + rat_of_Z 2)^3 * (- n + - rat_of_Z 2 + k)^2)).

Definition Q_flat (v : int -> int -> rat) (n_ k_ : int) : rat :=
Q_cf0_0 n_ k_ * v n_ k_ + Q_cf1_0 n_ k_ * v (int.shift 1 n_) k_ + Q_cf0_1 n_ k_ * v n_ (int.shift 1 k_).

Definition Q_seq := [:: [:: Q_cf0_0; Q_cf1_0]; [:: Q_cf0_1]].

Definition Q_horner := punk.biv_horner_seqop2 Q_seq.

