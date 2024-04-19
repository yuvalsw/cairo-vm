# References parsing with Nom

## Context
Hints embedded in Cairo code have access to the variables defined in the program. In the compiled JSON Cairo program, the `hints` key holds one entry for each hint embedded in the Cairo source code. Inside one of such entries, a key `reference_ids` can be found, containing a mapping between Cairo variable names used inside the hint and an id,

```json
    "reference_ids": {
        "__main__.main.var_a": 0,
        "__main__.main.var_b": 1 
        }
```
In the example above variables `var_a` and `var_b` are being mapped to 0 and 1, respectively. 

These ids are nothing more than the index of a reference inside the `references` list of the `reference_manager`, another key of the compiled JSON program.

```json
    "reference_manager": {
        "references": [
            {
                "ap_tracking_data": {
                    "group": 1,
                    "offset": 2
                },
                "pc": 3,
                "value": "[cast(ap + (-2), felt*)]"
            },
            {
                "ap_tracking_data": {
                    "group": 1,
                    "offset": 2
                },
                "pc": 3,
                "value": "[cast(ap + (-1), felt*)]"
            }
        ]
```
So here the elements 0 and 1 of the `references` list, hold information about variables `var_a` and `var_b`, respectively.

The `value` key is the one that holds information about the value of that variable in memory and its type. The parsing of these strings is done with Nom.

**Note**: References that appear in the `references` list are not limited to the ones used by hints. This document will focus on the references that have been found related to hints.

---

## Grammar
The final value of the variable is always the result of the casting function followed by a dereference `[]` when needed. 
The most common formats of these are as follows:

1. ```[cast(reg + offset1, type)]```
2. ```[cast([reg + offset1] + offset2, type)]```
3. ```cast(reg + offset1, type)```
4. ```cast([reg + offset1] + offset2, type)```

Cases 3 and 4 are just the non-dereferenced versions of 1 and 2. Here `reg` can take the value of either **ap** or **fp**, and `offset1` and `offset2` could be any signed integer. When negative, the minus sign is always set inside a parenthesis. See the example below for clarification.
 `type` is generally a field element pointer (`felt*`) or simple a field element (`felt`), but can be any other Cairo type or struct.


**Example: ```[cast(fp + (-1), felt*)]```**

Suppose that the `fp` register is holding the address (1, 3). Then `fp + (-1)` would yield address (1, 2). Suppose now that (1, 2) holds the value 5. Then, the value associated with this reference will be 5 after applying the dereference operator `[]`. 

There are some other, more rare cases of reference values found when implementing hints that were considered in the parsing,

* ```cast(number, felt)```
* ```[cast(reg + offset1 + offset2, type)]```
* ```[cast([[reg + offset1] + offset2], type)]```

## To do
For the moment the type of the reference is not being used, this will be included in the future to make the hints code cleaner.

## Nom useful references
* https://github.com/Geal/nom/blob/main/doc/choosing_a_combinator.md
* https://blog.adamchalmers.com/nom-chars/
* https://iximiuz.com/en/posts/rust-writing-parsers-with-nom/
* https://blog.logrocket.com/parsing-in-rust-with-nom/



