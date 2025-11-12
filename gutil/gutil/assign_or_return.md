# ASSIGN_OR_RETURN Macro Explanation

The `ASSIGN_OR_RETURN` macro may look complicated at first, but ultimately does
not breaks down to a few different macros. To get an overview of what
`ASSIGN_OR_RETURN` does, skip to the [ASSIGN_OR_RETURN](#ASSIGN_OR_RETURN)
section.

Below is a call graph of the macros:

```
ASSIGN_OR_RETURN  # Initial dispatch.
      |
      |_______ __ASSIGN_OR_RETURN_PICK            # Selects the macro to invoke
                          |
               2-----< # Params >-----3
               |                      |
               |                      |
    __ASSIGN_OR_RETURN __ASSIGN_OR_RETURN_STREAM  # Performs the actual logic
               |                      |
               |                      |
               |                      |
           __ASSIGN_OR_RETURN_VAL(__LINE__)       # Resolves the __LINE__ arg.
                          |
           __ASSIGN_OR_RETURN_VAL_INDIRECT        # Creates a unique value
```

## Individual Macro Descriptions

Descriptions are given in a bottom-up manner in relation to the previous graph.

### \_\_ASSIGN\_OR\_RETURN\_VAL\_DIRECT

`__ASSIGN_OR_RETURN_VAL_DIRECT(arg)` creates a unique variable name:
`__ASSIGN_OR_RETURN_RESULT_[arg]`. This helps the other `__ASSIGN_OR_RETURN`
macros save values in the caller's scope while minimizing the risk of conflict
with any existing variable.

#### Macro

```c++
#define __ASSIGN_OR_RETURN_VAL_DIRECT(arg) \
  __ASSIGN_OR_RETURN_RESULT_##arg
```

#### Constraints

`__ASSIGN_OR_RETURN_VAL_DIRECT` utilizes the argument name, not the value. It
does not invoke any macro that is passed in as an argument (e.g. `__LINE__`).
Therefore, we suggest users invoke the wrapper macro `__ASSIGN_OR_RETURN_VAL`
described in the next section.

#### Examples

Code                                      | Resolves to
----------------------------------------- | ------------------------------------
`__ASSIGN_OR_RETURN_VAL_DIRECT(__LINE__)` | `__ASSIGN_OR_RETURN_RESULT___LINE__`
`__ASSIGN_OR_RETURN_VAL_DIRECT()`         | `__ASSIGN_OR_RETURN_RESULT`
`__ASSIGN_OR_RETURN_VAL_DIRECT(HELLO)`    | `__ASSIGN_OR_RETURN_RESULT_HELLO`

### \_\_ASSIGN\_OR\_RETURN\_VAL

`__ASSIGN_OR_RETURN_VAL(arg)` is a wrapper around
`__ASSIGN_OR_RETURN_VAL_DIRECT`, described in the previous section. This macro
evaluates its argument before passing it to `__ASSIGN_OR_RETURN_VAL`.

#### Macro

```c++
#define __ASSIGN_OR_RETURN_VAL(arg) \
  __ASSIGN_OR_RETURN_VAL_DIRECT(arg)
```

#### Examples

Line | Code                               | Resolves to
---- | ---------------------------------- | ---------------------------------
173  | `__ASSIGN_OR_RETURN_VAL(__LINE__)` | `__ASSIGN_OR_RETURN_RESULT_173`
834  | `__ASSIGN_OR_RETURN_VAL(__LINE__)` | `__ASSIGN_OR_RETURN_RESULT_834`
-    | `__ASSIGN_OR_RETURN_VAL()`         | `__ASSIGN_OR_RETURN_RESULT_`
-    | `__ASSIGN_OR_RETURN_VAL(HELLO)`    | `__ASSIGN_OR_RETURN_RESULT_HELLO`

### \_\_ASSIGN\_OR\_RETURN

`__ASSIGN_OR_RETURN(dest, expr)` evalutes an expression returning a StatusOr
object. If the resulting StatusOr contains a value (is ok), the value is saved
to `dest`. Otherwise, the StatusOr's error status is returned.

#### Macro

```c++
#define __ASSIGN_OR_RETURN(dest, expr)                \
  auto __ASSIGN_OR_RETURN_VAL(__LINE__) = expr;       \
  if (!__ASSIGN_OR_RETURN_VAL(__LINE__).ok()) {       \
    return __ASSIGN_OR_RETURN_VAL(__LINE__).status(); \
  }                                                   \
  dest = __ASSIGN_OR_RETURN_VAL(__LINE__).value()
```

#### Examples

`__ASSIGN_OR_RETURN(int val, StatusOrFunc());` @ line **127** resolves to:

```c++
auto __ASSIGN_OR_RETURN_VAL_127 = StatusorFunc();
if (!__ASSIGN_OR_RETURN_VAL_127.ok()) {
  return __ASSIGN_OR_RETURN_VAL_127.status();
}
dest = __ASSIGN_OR_RETURN_VAL_127.value();
```

### \_\_ASSIGN\_OR\_RETURN\_STREAM

`__ASSIGN_OR_RETURN_STREAM(dest, expr, stream)` works similarly to
`__ASSIGN_OR_RETURN` described in the previous section. However, it has the
addition of a `stream` input which allows the caller to control a
`StatusBuilder` object to inject or log information. The `stream` parameter is
must be a command assuming a StatusOr object already exists with the name `_`.

#### Macro

```c++
#define __ASSIGN_OR_RETURN_STREAM(dest, expr, stream)     \
  auto __ASSIGN_OR_RETURN_VAL(__LINE__) = expr;           \
  if (!__ASSIGN_OR_RETURN_VAL(__LINE__).ok()) {           \
    return status::StatusBuilderHolder(    \
               __ASSIGN_OR_RETURN_VAL(__LINE__).status()) \
        .builder##stream;                                 \
  }                                                       \
  dest = __ASSIGN_OR_RETURN_VAL(__LINE__).value()
```

#### Examples

Assume all `__ASSIGN_OR_RETURN_STREAM` calls are made @ line **134**.

##### Example 1

```c++
// Assign Foo().value() to val if successful.
// If unsuccessful, append 'info' to the error message.
__ASSIGN_OR_RETURN_STREAM(int val, Foo(), _ << "info")
```

resolves to

```c++
auto __ASSIGN_OR_RETURN_VAL_134 = Foo();
if (!__ASSIGN_OR_RETURN_VAL_134.ok()) {
  return status::StatusBuilderHolder(
             __ASSIGN_OR_RETURN_VAL_134.status()).builder_ << "info";
}
dest = __ASSIGN_OR_RETURN_VAL_134.value();
```

##### Example 2

```c++
// Assign Foo().value() to val if successful.
// If unsuccessful, append 'info' to the error message and log the error.
__ASSIGN_OR_RETURN_STREAM(int val, Foo(), _.LogError() << "info")
```

resolves to

```c++
auto __ASSIGN_OR_RETURN_VAL_134 = Foo();
if (!__ASSIGN_OR_RETURN_VAL_134.ok())
  return status::StatusBuilderHolder(
             __ASSIGN_OR_RETURN_VAL_134.status()).builder_.LogError() << "info";
dest = __ASSIGN_OR_RETURN_VAL_134.value();
```

### \_\_ASSIGN\_OR\_RETURN\_PICK

`__ASSIGN_OR_RETURN_PICK(dest, expr, stream, func, ...)` returns a macro based
on the number of arguments provided for macros with up to 3 inputs (dest, expr,
and stream). This macro functions when the caller ensures the **fourth**
argument is the macro to return.

The expected usage is:

```c++
FOO(...)                                                            \
  __ASSIGN_OR_RETURN_PICK(__VA_ARGS__, FOO_3INPUTS, [FOO_2INPUTS],  \
                          [FOO_1INPUT], [FOO_0INPUTS])(__VA_ARGS__) \
```

#### Macro

```c++
#define __ASSIGN_OR_RETURN_PICK(dest, expr, stream, func, ...) func
```

#### Examples

```c++
SUM_3(arg1, arg2, arg3) arg1 + arg2 + arg3
SUM_2(arg1, arg2) arg1 + arg2
SUM_1(arg1) arg1
SUM_0() 0

SUM(...)
  __ASSIGN_OR_RETURN_PICK(__VA_ARGS__, SUM_3, SUM_2, SUM_1, SUM_0)(__VA_ARGS__)

std::cout << SUM() << std::endl;  // 0
std::cout << SUM(15) << std::endl;  // 15
std::cout << SUM(15, 5) << std::endl;  // 20
std::cout << SUM(15, 5, 1) << std::endl;  // 21
```

Detail for 3-argument call `SUM(15, 5, 1)`

```c++
// SUM with __VA_ARGS__ expansion
//               Fourth argument --v
__ASSIGN_OR_RETURN_PICK(15, 5, 1, SUM_3, SUM2, SUM_1, SUM_0)(15, 5, 1)

// __ASSIGN_OR_RETURN_PICK expansion
SUM_3(15, 5, 1)
```

Detail for 2-argument call `SUM(15, 5)`

```c++
// SUM with __VA_ARGS__ expansion
//                   Fourth argument --v
__ASSIGN_OR_RETURN_PICK(15, 5, SUM_3, SUM2, SUM_1, SUM_0)(15, 5)

// __ASSIGN_OR_RETURN_PICK expansion
SUM_2(15, 5)
```

Detail for 1-argument call `SUM(15)`

```c++
// SUM with __VA_ARGS__ expansion
//                      Fourth argument --v
__ASSIGN_OR_RETURN_PICK(15, SUM_3, SUM2, SUM_1, SUM_0)(15)

// __ASSIGN_OR_RETURN_PICK expansion
SUM_1(15)
```

Detail for 0-argument call `SUM()`

```c++
// SUM with __VA_ARGS__ expansion
//                          Fourth argument --v
__ASSIGN_OR_RETURN_PICK(SUM_3, SUM2, SUM_1, SUM_0)()

// __ASSIGN_OR_RETURN_PICK expansion
SUM_0()
```

## ASSIGN\_OR\_RETURN {#ASSIGN_OR_RETURN}

The `ASSIGN_OR_RETURN(...)` macro takes in up to three arguments:

1.  The value destination (if successful).
    *   The destination may be an existing variable (e.g. `foo`) or a new
        variable declaration (e.g. `int foo`).
2.  The expression to evaluate (must return StatusOr).
3.  An *optional* StatusBuilder command. This command must be presented with the
    assumption that the resulting StatusBuilder is named `_`. Example:
    `_.LogError() << "info"`.

`ASSIGN_OR_RETURN` evaluates the expression (second parameter). If the resulting
StatusOr contains a value (is ok), the the destination (first parameter) is set
to the StatusOr value. Otherwise, the error StatusOr (error) status is returned
with optional StatusBuilder modifications (third parameter).

### Macro

```c++
#define ASSIGN_OR_RETURN(...)                                     \
  __ASSIGN_OR_RETURN_PICK(__VA_ARGS__, __ASSIGN_OR_RETURN_STREAM, \
                          __ASSIGN_OR_RETURN)                     \
  (__VA_ARGS__)
```

### Examples

#### Basic ASSIGN\_OR\_RETURN

```c++
Line |
173  | ASSIGN_OR_RETURN(bool val, Foo());
```

Resolves to:

```c++
auto __ASSIGN_OR_RETURN_RESULT_173 = Foo();
if (!__ASSIGN_OR_RETURN_RESULT_173.ok()) {
  return __ASSIGN_OR_RETURN_RESULT_173.status();
}
bool val = __ASSIGN_OR_RETURN_RESULT_173;
```

#### ASSIGN\_OR\_RETURN with StatusBuilder

```c++
Line |
173  | ASSIGN_OR_RETURN(bool val, Foo(), _.LogError() << "info");
```

Resolves to:

```c++
auto __ASSIGN_OR_RETURN_RESULT_173 = Foo();
if (!__ASSIGN_OR_RETURN_RESULT_173.ok()) {
  return status::StatusBuilderHolder(
             __ASSIGN_OR_RETURN_RESULT_173.status())
             .builder_.LogError()
         << "info";
}
bool val = __ASSIGN_OR_RETURN_RESULT_173;
```
