This is a formalization of the results described in the paper
"Non-accessible localizations" available at my [web page](https://jdc.math.uwo.ca/papers.html).
A link to a talk is also available at that page.

Here is a mapping between the results in the paper and the formalization:

```
Proposition 2.2:  Smallness.issmall_n_image
Lemma 2.3:        Smallness.islocally_small_trunc
Lemma 2.4:        Smallness.islocally_small_truncmap
Lemma 2.5:        Smallness.issmall_truncmap_connected
Theorem 2.6:      Smallness.issmall_iff_locally_small_truncated
Corollary 2.7:    Smallness.issmall_truncmap_small_truncation
Remark 2.9:       Smallness.issmall_inhabited_issmall
Proposition 3.2:  NonAccessible.restrict_O
Theorem 3.3:      NonAccessible.nonaccessible_localization
```

You will likely need to edit the _CoqProject file to make this build on your system.

Also, the universe variables are sensitive to the library version (and maybe the Coq version):

- Commit 0bed3109 from February 3, 2024, builds with Coq 8.18.0 and Coq-HoTT library version fc8e5b46 from February 6, 2024.

- Commit 9015e6d0 from January 1, 2024, builds with Coq 8.18.0 and Coq-HoTT library version 698ca2fb from January 1, 2024.

- Commit 9943c0a2 from September 29, 2023, builds with Coq 8.18.0 and Coq-HoTT library version a3bde181 from September 27, 2023.

- Commit 1b8e486b from February 26, 2023, builds with Coq 8.16.1 and Coq-HoTT library version 8d1c6a7e from February 26, 2023.

- Commit 33ee3baf from June 6, 2022 builds with Coq 8.15.1 and Coq-HoTT library version bca7ccfa from May 23, 2022.
