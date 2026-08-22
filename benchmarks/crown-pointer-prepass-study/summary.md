# CROWN pointer pre-pass study

Raw pointers are expanded-AST `TyKind::Ptr` occurrences. Unsafe features are counted with `crat-finder unsafe` and normalized exactly as in `crat-workspace/scripts/post_summarize_unsafe.py`.

## Aggregate remaining raw pointers

| with five pre-passes | without five pre-passes | additional without |
| ---: | ---: | ---: |
| 36339 | 36206 | -133 |

## Aggregate raw pointers at sub-pass boundaries

| sub-pass | before | after | eliminated (net) |
| --- | ---: | ---: | ---: |
| struct_arrays | 45662 | 45662 | 0 |
| struct_param_fields | 45662 | 45662 | 0 |
| epoch_split | 45662 | 45773 | -111 |
| aliasing | 45773 | 45773 | 0 |
| array_local_provenance | 45773 | 45927 | -154 |

Negative elimination means that the preparatory pass introduced raw-pointer type occurrences.

## Main replacement context

| configuration | input to `replace_local_borrows` | after replacement | eliminated by replacement |
| --- | ---: | ---: | ---: |
| with five pre-passes | 45927 | 39761 | 6166 |
| without five pre-passes | 45662 | 39606 | 6056 |

## Aggregate remaining unsafe features

| feature | with five pre-passes | without five pre-passes | additional without |
| --- | ---: | ---: | ---: |
| alloc | 180 | 182 | 2 |
| deref | 6673 | 6708 | 35 |
| fnptr | 134 | 134 | 0 |
| lib | 4860 | 4860 | 0 |
| offset | 3077 | 3055 | -22 |
| static | 9908 | 9908 | 0 |
| std | 7261 | 7166 | -95 |
| transmute | 14 | 14 | 0 |
| union | 233 | 233 | 0 |
| **total** | **32340** | **32260** | **-80** |

## Remaining raw pointers by benchmark

| benchmark | with | without | additional without |
| --- | ---: | ---: | ---: |
| avl | 0 | 0 | 0 |
| bst | 0 | 0 | 0 |
| genann-1.0.0 | 363 | 365 | 2 |
| json.h | 0 | 0 | 0 |
| libzahl-1.0 | 9253 | 9253 | 0 |
| quadtree-0.1.0 | 244 | 244 | 0 |
| tulipindicators | 8355 | 8356 | 1 |
| binn-3.0 | 10130 | 10015 | -115 |
| buffer-0.4.0 | 323 | 323 | 0 |
| heman | 0 | 0 | 0 |
| libcsv | 412 | 410 | -2 |
| lil | 899 | 894 | -5 |
| rgba | 276 | 276 | 0 |
| urlparser | 1014 | 1016 | 2 |
| brotli-1.0.9 | 2554 | 2543 | -11 |
| bzip2 | 784 | 788 | 4 |
| ht | 0 | 0 | 0 |
| libtree-3.1.1 | 425 | 416 | -9 |
| lodepng | 0 | 0 | 0 |
| robotfindskitten | 1307 | 1307 | 0 |
