import Euclid.Sorts.Primitives
import Euclid.Relations.Line

namespace Euclid

  /--
    三角形
  -/
  structure Triangle where
    a: Point
    b: Point
    c: Point
    h: ¬ Point.on_same_line a b c

end Euclid
