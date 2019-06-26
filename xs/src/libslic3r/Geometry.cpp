#include "Geometry.hpp"
#include "ClipperUtils.hpp"
#include "ExPolygon.hpp"
#include "Line.hpp"
#include "Log.hpp"
#include "PolylineCollection.hpp"
#include "clipper.hpp"
#include <algorithm>
#include <numeric>
#include <cassert>
#include <cmath>
#include <list>
#include <map>
#include <set>
#include <utility>
#include <stack>
#include <vector>

#ifdef SLIC3R_DEBUG
#include "SVG.hpp"
#endif

#ifdef SLIC3R_DEBUG
namespace boost { namespace polygon {

// The following code for the visualization of the boost Voronoi diagram is based on:
//
// Boost.Polygon library voronoi_graphic_utils.hpp header file
//          Copyright Andrii Sydorchuk 2010-2012.
// Distributed under the Boost Software License, Version 1.0.
//    (See accompanying file LICENSE_1_0.txt or copy at
//          http://www.boost.org/LICENSE_1_0.txt)
template <typename CT>
class voronoi_visual_utils {
 public:
  // Discretize parabolic Voronoi edge.
  // Parabolic Voronoi edges are always formed by one point and one segment
  // from the initial input set.
  //
  // Args:
  //   point: input point.
  //   segment: input segment.
  //   max_dist: maximum discretization distance.
  //   discretization: point discretization of the given Voronoi edge.
  //
  // Template arguments:
  //   InCT: coordinate type of the input geometries (usually integer).
  //   Point: point type, should model point concept.
  //   Segment: segment type, should model segment concept.
  //
  // Important:
  //   discretization should contain both edge endpoints initially.
  template <class InCT1, class InCT2,
            template<class> class Point,
            template<class> class Segment>
  static
  typename enable_if<
    typename gtl_and<
      typename gtl_if<
        typename is_point_concept<
          typename geometry_concept< Point<InCT1> >::type
        >::type
      >::type,
      typename gtl_if<
        typename is_segment_concept<
          typename geometry_concept< Segment<InCT2> >::type
        >::type
      >::type
    >::type,
    void
  >::type discretize(
      const Point<InCT1>& point,
      const Segment<InCT2>& segment,
      const CT max_dist,
      std::vector< Point<CT> >* discretization) {
    // Apply the linear transformation to move start point of the segment to
    // the point with coordinates (0, 0) and the direction of the segment to
    // coincide the positive direction of the x-axis.
    CT segm_vec_x = cast(x(high(segment))) - cast(x(low(segment)));
    CT segm_vec_y = cast(y(high(segment))) - cast(y(low(segment)));
    CT sqr_segment_length = segm_vec_x * segm_vec_x + segm_vec_y * segm_vec_y;

    // Compute x-coordinates of the endpoints of the edge
    // in the transformed space.
    CT projection_start = sqr_segment_length *
        get_point_projection((*discretization)[0], segment);
    CT projection_end = sqr_segment_length *
        get_point_projection((*discretization)[1], segment);

    // Compute parabola parameters in the transformed space.
    // Parabola has next representation:
    // f(x) = ((x-rot_x)^2 + rot_y^2) / (2.0*rot_y).
    CT point_vec_x = cast(x(point)) - cast(x(low(segment)));
    CT point_vec_y = cast(y(point)) - cast(y(low(segment)));
    CT rot_x = segm_vec_x * point_vec_x + segm_vec_y * point_vec_y;
    CT rot_y = segm_vec_x * point_vec_y - segm_vec_y * point_vec_x;

    // Save the last point.
    Point<CT> last_point = (*discretization)[1];
    discretization->pop_back();

    // Use stack to avoid recursion.
    std::stack<CT> point_stack;
    point_stack.push(projection_end);
    CT cur_x = projection_start;
    CT cur_y = parabola_y(cur_x, rot_x, rot_y);

    // Adjust max_dist parameter in the transformed space.
    const CT max_dist_transformed = max_dist * max_dist * sqr_segment_length;
    while (!point_stack.empty()) {
      CT new_x = point_stack.top();
      CT new_y = parabola_y(new_x, rot_x, rot_y);

      // Compute coordinates of the point of the parabola that is
      // furthest from the current line segment.
      CT mid_x = (new_y - cur_y) / (new_x - cur_x) * rot_y + rot_x;
      CT mid_y = parabola_y(mid_x, rot_x, rot_y);

      // Compute maximum distance between the given parabolic arc
      // and line segment that discretize it.
      CT dist = (new_y - cur_y) * (mid_x - cur_x) -
          (new_x - cur_x) * (mid_y - cur_y);
      dist = dist * dist / ((new_y - cur_y) * (new_y - cur_y) +
          (new_x - cur_x) * (new_x - cur_x));
      if (dist <= max_dist_transformed) {
        // Distance between parabola and line segment is less than max_dist.
        point_stack.pop();
        CT inter_x = (segm_vec_x * new_x - segm_vec_y * new_y) /
            sqr_segment_length + cast(x(low(segment)));
        CT inter_y = (segm_vec_x * new_y + segm_vec_y * new_x) /
            sqr_segment_length + cast(y(low(segment)));
        discretization->push_back(Point<CT>(inter_x, inter_y));
        cur_x = new_x;
        cur_y = new_y;
      } else {
        point_stack.push(mid_x);
      }
    }

    // Update last point.
    discretization->back() = last_point;
  }

 private:
  // Compute y(x) = ((x - a) * (x - a) + b * b) / (2 * b).
  static CT parabola_y(CT x, CT a, CT b) {
    return ((x - a) * (x - a) + b * b) / (b + b);
  }

  // Get normalized length of the distance between:
  //   1) point projection onto the segment
  //   2) start point of the segment
  // Return this length divided by the segment length. This is made to avoid
  // sqrt computation during transformation from the initial space to the
  // transformed one and vice versa. The assumption is made that projection of
  // the point lies between the start-point and endpoint of the segment.
  template <class InCT,
            template<class> class Point,
            template<class> class Segment>
  static
  typename enable_if<
    typename gtl_and<
      typename gtl_if<
        typename is_point_concept<
          typename geometry_concept< Point<int> >::type
        >::type
      >::type,
      typename gtl_if<
        typename is_segment_concept<
          typename geometry_concept< Segment<long> >::type
        >::type
      >::type
    >::type,
    CT
  >::type get_point_projection(
      const Point<CT>& point, const Segment<InCT>& segment) {
    CT segment_vec_x = cast(x(high(segment))) - cast(x(low(segment)));
    CT segment_vec_y = cast(y(high(segment))) - cast(y(low(segment)));
    CT point_vec_x = x(point) - cast(x(low(segment)));
    CT point_vec_y = y(point) - cast(y(low(segment)));
    CT sqr_segment_length =
        segment_vec_x * segment_vec_x + segment_vec_y * segment_vec_y;
    CT vec_dot = segment_vec_x * point_vec_x + segment_vec_y * point_vec_y;
    return vec_dot / sqr_segment_length;
  }

  template <typename InCT>
  static CT cast(const InCT& value) {
    return static_cast<CT>(value);
  }
};

} } // namespace boost::polygon
#endif

using namespace boost::polygon;  // provides also high() and low()

namespace Slic3r { namespace Geometry {

static bool
sort_points (Point a, Point b)
{
    return (a.x < b.x) || (a.x == b.x && a.y < b.y);
}

/* This implementation is based on Andrew's monotone chain 2D convex hull algorithm */
Polygon
convex_hull(Points points)
{
    assert(points.size() >= 3);
    // sort input points
    std::sort(points.begin(), points.end(), sort_points);
    
    int n = points.size(), k = 0;
    Polygon hull;
    hull.points.resize(2*n);

    // Build lower hull
    for (int i = 0; i < n; i++) {
        while (k >= 2 && points[i].ccw(hull.points[k-2], hull.points[k-1]) <= 0) k--;
        hull.points[k++] = points[i];
    }

    // Build upper hull
    for (int i = n-2, t = k+1; i >= 0; i--) {
        while (k >= t && points[i].ccw(hull.points[k-2], hull.points[k-1]) <= 0) k--;
        hull.points[k++] = points[i];
    }

    hull.points.resize(k);
    
    assert( hull.points.front().coincides_with(hull.points.back()) );
    hull.points.pop_back();
    
    return hull;
}

Polygon
convex_hull(const Polygons &polygons)
{
    Points pp;
    for (Polygons::const_iterator p = polygons.begin(); p != polygons.end(); ++p) {
        pp.insert(pp.end(), p->points.begin(), p->points.end());
    }
    return convex_hull(pp);
}

/* accepts an arrayref of points and returns a list of indices
   according to a nearest-neighbor walk */
void
chained_path(const Points &points, std::vector<Points::size_type> &retval, Point start_near)
{
    PointConstPtrs my_points;
    std::map<const Point*,Points::size_type> indices;
    my_points.reserve(points.size());
    for (Points::const_iterator it = points.begin(); it != points.end(); ++it) {
        my_points.push_back(&*it);
        indices[&*it] = it - points.begin();
    }
    
    retval.reserve(points.size());
    while (!my_points.empty()) {
        Points::size_type idx = start_near.nearest_point_index(my_points);
        start_near = *my_points[idx];
        retval.push_back(indices[ my_points[idx] ]);
        my_points.erase(my_points.begin() + idx);
    }
}

void
chained_path(const Points &points, std::vector<Points::size_type> &retval)
{
    if (points.empty()) return;  // can't call front() on empty vector
    chained_path(points, retval, points.front());
}

/* retval and items must be different containers */
template<class T>
void
chained_path_items(Points &points, T &items, T &retval)
{
    std::vector<Points::size_type> indices;
    chained_path(points, indices);
    for (std::vector<Points::size_type>::const_iterator it = indices.begin(); it != indices.end(); ++it)
        retval.push_back(items[*it]);
}
template void chained_path_items(Points &points, ClipperLib::PolyNodes &items, ClipperLib::PolyNodes &retval);

bool
directions_parallel(double angle1, double angle2, double max_diff)
{
    double diff = fabs(angle1 - angle2);
    max_diff += EPSILON;
    return diff < max_diff || fabs(diff - PI) < max_diff;
}

template<class T>
bool
contains(const std::vector<T> &vector, const Point &point)
{
    for (const T &it : vector)
        if (it.contains(point))
            return true;
    
    return false;
}
template bool contains(const Polygons &vector, const Point &point);
template bool contains(const ExPolygons &vector, const Point &point);

template<class T>
double
area(const std::vector<T> &vector)
{
    double area = 0;
    for (const T &it : vector)
        area += it.area();
    
    return area;
}
template double area(const Polygons &vector);

double
rad2deg(double angle)
{
    return angle / PI * 180.0;
}

double
rad2deg_dir(double angle)
{
    angle = (angle < PI) ? (-angle + PI/2.0) : (angle + PI/2.0);
    if (angle < 0) angle += PI;
    return rad2deg(angle);
}

double
deg2rad(double angle)
{
    return PI * angle / 180.0;
}

double
linint(double value, double oldmin, double oldmax, double newmin, double newmax)
{
    return (value - oldmin) * (newmax - newmin) / (oldmax - oldmin) + newmin;
}

Point
circle_taubin_newton(const Points& input, size_t cycles)
{
    return circle_taubin_newton(input.cbegin(), input.cend(), cycles);
}

Point
circle_taubin_newton(const Points::const_iterator& input_begin, const Points::const_iterator& input_end, size_t cycles)
{
    Pointfs tmp;
    tmp.reserve(std::distance(input_begin, input_end));
    std::transform(input_begin, input_end, std::back_inserter(tmp), [] (const Point& in) {return Pointf::new_unscale(in); } );
    return Point::new_scale(circle_taubin_newton(tmp.cbegin(), tmp.end(), cycles));
}

Pointf
circle_taubin_newton(const Pointfs& input, size_t cycles)
{
    return circle_taubin_newton(input.cbegin(), input.cend(), cycles);
}


/// Adapted from work in "Circular and Linear Regression: Fitting circles and lines by least squares", pg 126
/// Returns a point corresponding to the center of a circle for which all of the points from input_begin to input_end
/// lie on.
Pointf
circle_taubin_newton(const Pointfs::const_iterator& input_begin, const Pointfs::const_iterator& input_end, size_t cycles)
{
    // calculate the centroid of the data set
    const Pointf sum = std::accumulate(input_begin, input_end, Pointf(0,0));
    const size_t n = std::distance(input_begin, input_end);
    const double n_flt = static_cast<double>(n);
    const Pointf centroid { sum / n_flt };

    // Compute the normalized moments of the data set.
    double Mxx = 0, Myy = 0, Mxy = 0, Mxz = 0, Myz = 0, Mzz = 0;
    for (auto it = input_begin; it < input_end; ++it) {
        // center/normalize the data.
        double Xi {it->x - centroid.x};
        double Yi {it->y - centroid.y};
        double Zi {Xi*Xi + Yi*Yi};
        Mxy += (Xi*Yi);
        Mxx += (Xi*Xi);
        Myy += (Yi*Yi);
        Mxz += (Xi*Zi);
        Myz += (Yi*Zi);
        Mzz += (Zi*Zi);
    }

    // divide by number of points to get the moments
    Mxx /= n_flt;
    Myy /= n_flt;
    Mxy /= n_flt;
    Mxz /= n_flt;
    Myz /= n_flt;
    Mzz /= n_flt;

    // Compute the coefficients of the characteristic polynomial for the circle
    // eq 5.60
    const double Mz {Mxx + Myy}; // xx + yy = z
    const double Cov_xy {Mxx*Myy - Mxy*Mxy}; // this shows up a couple times so cache it here.
    const double C3 {4.0*Mz};
    const double C2 {-3.0*(Mz*Mz) - Mzz};
    const double C1 {Mz*(Mzz - (Mz*Mz)) + 4.0*Mz*Cov_xy - (Mxz*Mxz) - (Myz*Myz)};
    const double C0 {(Mxz*Mxz)*Myy + (Myz*Myz)*Mxx - 2.0*Mxz*Myz*Mxy - Cov_xy*(Mzz - (Mz*Mz))};

    const double C22 = {C2 + C2};
    const double C33 = {C3 + C3 + C3};

    // solve the characteristic polynomial with Newton's method.
    double xnew = 0.0;
    double ynew = 1e20;

    for (size_t i = 0; i < cycles; ++i) {
        const double yold {ynew};
        ynew = C0 + xnew * (C1 + xnew*(C2 + xnew * C3));
        if (std::abs(ynew) > std::abs(yold)) {
            Slic3r::Log::error("Geometry") << "Fit is going in the wrong direction.\n";
            return Pointf(std::nan(""), std::nan(""));
        }
        const double Dy {C1 + xnew*(C22 + xnew*C33)};

        const double xold {xnew};
        xnew = xold - (ynew / Dy);

        if (std::abs((xnew-xold) / xnew) < 1e-12) i = cycles; // converged, we're done here

        if (xnew < 0) {
            // reset, we went negative
            xnew = 0.0;
        }
    }
    
    // compute the determinant and the circle's parameters now that we've solved.
    double DET = xnew*xnew - xnew*Mz + Cov_xy;

    Pointf center {Pointf(Mxz * (Myy - xnew) - Myz * Mxy, Myz * (Mxx - xnew) - Mxz*Mxy)};
    center = center / DET / 2;

    return center + centroid;
    
}

/*
== Perl implementations for methods tested in geometry.t but not translated.  ==
== The first three are unreachable in the current perl code and the fourth is ==
== only called from ArcFitting which currently dies before reaching the call. ==
sub point_in_segment {
    my ($point, $line) = @_;

    my ($x, $y) = @$point;
    my $line_p = $line->pp;
    my @line_x = sort { $a <=> $b } $line_p->[A][X], $line_p->[B][X];
    my @line_y = sort { $a <=> $b } $line_p->[A][Y], $line_p->[B][Y];

    # check whether the point is in the segment bounding box
    return 0 unless $x >= ($line_x[0] - epsilon) && $x <= ($line_x[1] + epsilon)
        && $y >= ($line_y[0] - epsilon) && $y <= ($line_y[1] + epsilon);

    # if line is vertical, check whether point's X is the same as the line
    if ($line_p->[A][X] == $line_p->[B][X]) {
        return abs($x - $line_p->[A][X]) < epsilon ? 1 : 0;
    }

    # calculate the Y in line at X of the point
    my $y3 = $line_p->[A][Y] + ($line_p->[B][Y] - $line_p->[A][Y])
        * ($x - $line_p->[A][X]) / ($line_p->[B][X] - $line_p->[A][X]);
    return abs($y3 - $y) < epsilon ? 1 : 0;
}


# given a $polygon, return the (first) segment having $point
sub polygon_segment_having_point {
    my ($polygon, $point) = @_;

    foreach my $line (@{ $polygon->lines }) {
        return $line if point_in_segment($point, $line);
    }
    return undef;
}


# polygon must be simple (non complex) and ccw
sub polygon_is_convex {
    my ($points) = @_;
    for (my $i = 0; $i <= $#$points; $i++) {
        my $angle = angle3points($points->[$i-1], $points->[$i-2], $points->[$i]);
        return 0 if $angle < PI;
    }
    return 1;
}

# this assumes a CCW rotation from $p2 to $p3 around $p1
sub angle3points {
    my ($p1, $p2, $p3) = @_;
    # p1 is the center

    my $angle = atan2($p2->[X] - $p1->[X], $p2->[Y] - $p1->[Y])
              - atan2($p3->[X] - $p1->[X], $p3->[Y] - $p1->[Y]);

    # we only want to return only positive angles
    return $angle <= 0 ? $angle + 2*PI() : $angle;
}
*/


class ArrangeItem {
    public:
    Pointf pos;
    size_t index_x, index_y;
    coordf_t dist;
};
class ArrangeItemIndex {
    public:
    coordf_t index;
    ArrangeItem item;
    ArrangeItemIndex(coordf_t _index, ArrangeItem _item) : index(_index), item(_item) {};
};

bool
arrange(size_t total_parts, const Pointf &part_size, coordf_t dist, const BoundingBoxf* bb, Pointfs &positions)
{
    positions.clear();

    Pointf part = part_size;

    // use actual part size (the largest) plus separation distance (half on each side) in spacing algorithm
    part.x += dist;
    part.y += dist;
    
    Pointf area;
    if (bb != NULL && bb->defined) {
        area = bb->size();
    } else {
        // bogus area size, large enough not to trigger the error below
        area.x = part.x * total_parts;
        area.y = part.y * total_parts;
    }
    
    // this is how many cells we have available into which to put parts
    size_t cellw = floor((area.x + dist) / part.x);
    size_t cellh = floor((area.y + dist) / part.y);
    if (total_parts > (cellw * cellh))
        return false;
    
    // total space used by cells
    Pointf cells(cellw * part.x, cellh * part.y);
    
    // bounding box of total space used by cells
    BoundingBoxf cells_bb;
    cells_bb.merge(Pointf(0,0)); // min
    cells_bb.merge(cells);  // max
    
    // center bounding box to area
    cells_bb.translate(
        (area.x - cells.x) / 2,
        (area.y - cells.y) / 2
    );
    
    // list of cells, sorted by distance from center
    std::vector<ArrangeItemIndex> cellsorder;
    
    // work out distance for all cells, sort into list
    for (size_t i = 0; i <= cellw-1; ++i) {
        for (size_t j = 0; j <= cellh-1; ++j) {
            coordf_t cx = linint(i + 0.5, 0, cellw, cells_bb.min.x, cells_bb.max.x);
            coordf_t cy = linint(j + 0.5, 0, cellh, cells_bb.min.y, cells_bb.max.y);
            
            coordf_t xd = fabs((area.x / 2) - cx);
            coordf_t yd = fabs((area.y / 2) - cy);
            
            ArrangeItem c;
            c.pos.x = cx;
            c.pos.y = cy;
            c.index_x = i;
            c.index_y = j;
            c.dist = xd * xd + yd * yd - fabs((cellw / 2) - (i + 0.5));
            
            // binary insertion sort
            {
                coordf_t index = c.dist;
                size_t low = 0;
                size_t high = cellsorder.size();
                while (low < high) {
                    size_t mid = (low + ((high - low) / 2)) | 0;
                    coordf_t midval = cellsorder[mid].index;
                    
                    if (midval < index) {
                        low = mid + 1;
                    } else if (midval > index) {
                        high = mid;
                    } else {
                        cellsorder.insert(cellsorder.begin() + mid, ArrangeItemIndex(index, c));
                        goto ENDSORT;
                    }
                }
                cellsorder.insert(cellsorder.begin() + low, ArrangeItemIndex(index, c));
            }
            ENDSORT: ;
        }
    }
    
    // the extents of cells actually used by objects
    coordf_t lx = 0;
    coordf_t ty = 0;
    coordf_t rx = 0;
    coordf_t by = 0;

    // now find cells actually used by objects, map out the extents so we can position correctly
    for (size_t i = 1; i <= total_parts; ++i) {
        ArrangeItemIndex c = cellsorder[i - 1];
        coordf_t cx = c.item.index_x;
        coordf_t cy = c.item.index_y;
        if (i == 1) {
            lx = rx = cx;
            ty = by = cy;
        } else {
            if (cx > rx) rx = cx;
            if (cx < lx) lx = cx;
            if (cy > by) by = cy;
            if (cy < ty) ty = cy;
        }
    }
    // now we actually place objects into cells, positioned such that the left and bottom borders are at 0
    for (size_t i = 1; i <= total_parts; ++i) {
        ArrangeItemIndex c = cellsorder.front();
        cellsorder.erase(cellsorder.begin());
        coordf_t cx = c.item.index_x - lx;
        coordf_t cy = c.item.index_y - ty;
        
        positions.push_back(Pointf(cx * part.x, cy * part.y));
    }
    
    if (bb != NULL && bb->defined) {
        for (Pointfs::iterator p = positions.begin(); p != positions.end(); ++p) {
            p->x += bb->min.x;
            p->y += bb->min.y;
        }
    }
    
    return true;
}

double point_distance( Point p, Point s1, Point s2, Pointf normal, bool infinite ){

    // TODO: normal might need to be normalized ( check translation vector )
    Pointf dir(normal.y, -normal.x);


    double pdot = p.x*dir.x + p.y*dir.y;
    double s1dot = s1.x*dir.x + s1.y*dir.y;
    double s2dot = s2.x*dir.x + s2.y*dir.y;

    double pdotnorm = p.x*normal.x + p.y*normal.y;
    double s1dotnorm = s1.x*normal.x + s1.y*normal.y;
    double s2dotnorm = s2.x*normal.x + s2.y*normal.y;

    if(!infinite){
        if (((pdot<s1dot || almost_equal(pdot, s1dot)) && (pdot<s2dot || almost_equal(pdot, s2dot))) || ((pdot>s1dot || almost_equal(pdot, s1dot)) && (pdot>s2dot || almost_equal(pdot, s2dot)))){
            return -1; // dot doesn't collide with segment, or lies directly on the vertex
        }
        if ((almost_equal(pdot, s1dot) && almost_equal(pdot, s2dot)) && (pdotnorm>s1dotnorm && pdotnorm>s2dotnorm)){
            return fmin(pdotnorm - s1dotnorm, pdotnorm - s2dotnorm);
        }
        if ((almost_equal(pdot, s1dot) && almost_equal(pdot, s2dot)) && (pdotnorm<s1dotnorm && pdotnorm<s2dotnorm)){
            return -fmin(s1dotnorm-pdotnorm, s2dotnorm-pdotnorm);
        }
    }

    return -(pdotnorm - s1dotnorm + (s1dotnorm - s2dotnorm)*(s1dot - pdot)/(s1dot - s2dot));
}

double segment_distance(Point A, Point B, Point E, Point F, Pointf direction) {
    Pointf normal(direction.y, -direction.x);
    Pointf reverse(-direction.x, -direction.y);


    double dotA = A.x*normal.x + A.y*normal.y;
    double dotB = B.x*normal.x + B.y*normal.y;
    double dotE = E.x*normal.x + E.y*normal.y;
    double dotF = F.x*normal.x + F.y*normal.y;

    double crossA = A.x*direction.x + A.y*direction.y;
    double crossB = B.x*direction.x + B.y*direction.y;
    double crossE = E.x*direction.x + E.y*direction.y;
    double crossF = F.x*direction.x + F.y*direction.y;

    double ABmin = fmin(dotA,dotB);//? dotA : dotB;
    double ABmax = fmax(dotA,dotB);// ? dotA : dotB;

    double EFmax = fmax(dotE,dotF);//? dotE : dotF;
    double EFmin = fmax(dotE, dotF);//? dotE : dotF;

    // segments that will merely touch at one point
    if(almost_equal(ABmax, EFmin ) || almost_equal(ABmin, EFmax )){
        return -1;
    }
    // segments miss eachother completely
    if(ABmax < EFmin || ABmin > EFmax){
        return -1;
    }

    double overlap;

    if((ABmax > EFmax && ABmin < EFmin) || (EFmax > ABmax && EFmin < ABmin)){
        overlap = 1;
    }
    else{
        double minMax =  fmin(ABmax , EFmax);//? ABmax : EFmax;
        double maxMin = fmax(ABmin ,  EFmin);//? ABmin : EFmin;

        double maxMax = fmax(ABmax, EFmax);
        double minMin = fmin(ABmin, EFmin);

        overlap = (minMax-maxMin)/(maxMax-minMin);
    }

    double crossABE = (E.y - A.y) * (B.x - A.x) - (E.x - A.x) * (B.y - A.y);
    double crossABF = (F.y - A.y) * (B.x - A.x) - (F.x - A.x) * (B.y - A.y);

    // lines are colinear
    if(almost_equal(crossABE,0) && almost_equal(crossABF,0)){

        Pointf ABnorm ( B.y-A.y, A.x-B.x);
        Pointf EFnorm ( F.y-E.y,  E.x-F.x);

        double ABnormlength = sqrt(ABnorm.x*ABnorm.x + ABnorm.y*ABnorm.y);
        ABnorm.x /= ABnormlength;
        ABnorm.y /= ABnormlength;

        double EFnormlength = sqrt(EFnorm.x*EFnorm.x + EFnorm.y*EFnorm.y);
        EFnorm.x /= EFnormlength;
        EFnorm.y /= EFnormlength;

        // segment normals must point in opposite directions
        if(fabs(ABnorm.y * EFnorm.x - ABnorm.x * EFnorm.y) < epsilon && ABnorm.y * EFnorm.y + ABnorm.x * EFnorm.x < 0){
            // normal of AB segment must point in same direction as given direction vector
            double normdot = ABnorm.y * direction.y + ABnorm.x * direction.x;
            // the segments merely slide along eachother
            if(almost_equal(normdot,0)){
                return -1;
            }
            if(normdot < 0){
                return 0;
            }
        }
        return -1;
    }

    std::vector<double> distances;
    // coincident points
    if(almost_equal(dotA, dotE)){
        distances.push_back(crossA-crossE);
    }
    else if(almost_equal(dotA, dotF)){
        distances.push_back(crossA-crossF);
    }
    else if(dotA > EFmin && dotA < EFmax){
        bool collide = false;
        double d = point_distance(A,E,F,reverse);
        if( d != -1 && almost_equal(d, 0)){ //  A currently touches EF, but AB is moving away from EF
            double dB = point_distance(B,E,F,reverse, true);
            if(dB < 0 || almost_equal(dB*overlap,0)){
                d = -1;
            }
        }
        if(d != -1){
            distances.push_back(d);
        }
    }


    if(almost_equal(dotB, dotE)){
        distances.push_back(crossB-crossE);
    }
    else if(almost_equal(dotB, dotF)){
        distances.push_back(crossB-crossF);
    }
    else if(dotB > EFmin && dotB < EFmax){
        double d = point_distance(B,E,F,reverse);

        if(d != -1 && almost_equal(d, 0)){ // crossA>crossB A currently touches EF, but AB is moving away from EF
            double dA = point_distance(A,E,F,reverse,true);
            if(dA < 0 || almost_equal(dA*overlap,0)){
                d = -1;
            }
        }
        if(d != -1){
            distances.push_back(d);
        }
    }
    if(dotE > ABmin && dotE < ABmax){
        double d = point_distance(E,A,B,direction);
        if(d != -1 && almost_equal(d, 0)){ // crossF<crossE A currently touches EF, but AB is moving away from EF
            double dF = point_distance(F,A,B,direction, true);
            if(dF < 0 || almost_equal(dF*overlap,0)){
                d = -1;
            }
        }
        if(d != -1){
            distances.push_back(d);
        }
    }



    if(dotF > ABmin && dotF < ABmax){
        double d = point_distance(F,A,B,direction);
        if(d != -1 && almost_equal(d, 0)){ // && crossE<crossF A currently touches EF, but AB is moving away from EF
            double dE = point_distance(E,A,B,direction, true);
            if(dE < 0 || almost_equal(dE*overlap,0)){
                d = -1;
            }
        }
        if(d != -1){
            distances.push_back(d);
        }
    }

    if(distances.size() == 0){
        return -1;
    }

    return 0;
}
double polygon_slide_distance(Polygon A, Polygon B, Point offset, TranslationVector translationVector) {


    Pointf dir = translationVector.normalize();
    Pointf normal(dir.y, -dir.x);
    Pointf reverse(-dir.x, -dir.y);
    Points & edgeA = A.points;
    Points & edgeB = B.points;
    double distance = -1 ;
    for( int i = 0; i < edgeA.size()-1; ++i){
        for(int j = 0;j < edgeB.size()-1; ++j){

            Point A1(A.points[i]);

            Point A2(edgeA[j+1]);

            Point B1(edgeB[i]+offset);

            Point B2(edgeB[i+1]+offset);

            if(almost_equal(A1,A2) || almost_equal(B1,B2)){
                continue; // extremely small line
            }

            // for these two edges calculate the minimum distance one of them can travel in the given direction before intersection
            double d = segment_distance(A1, A2, B1, B2, dir );

            if( d > 0){
                if( distance == -1 || d < distance){
                    distance = d;
                }
            }

        }
    }
    return distance;
}
Polygon no_fit_polygon(Polygon A, Polygon B) {
    Polygon nfp;
    if(A.points.size()<3 || B.points.size()<3 )
        return nfp;

    // Make sure that A and B are both anti-clockwise
    // TODO: see if this would be taken care of before calling the function
    A.make_counter_clockwise();
    B.make_counter_clockwise();

    // Translate the polygon B such that it's highest point is at A's lowest point
    // that way we can make sure that B will be touching A without intersection

    // First we get A's bottom point
    Point min_a(A.points[0]);
    int min_a_index = 0;
    for(int i = 1;i<A.points.size();++i){
        if(min_a.y<A.points[i].y){
            min_a = A.points[i];
            min_a_index=i;
        }
    }
    // Now we get B's Top point
    Point max_b(B.points[0]);
    int max_b_index = 0;
    for(int i = 1;i<B.points.size();++i){
        if(max_b.y<B.points[i].y){
            max_b = B.points[i];
            max_b_index=i;
        }
    }
    // This offset will be added to every point in B to translate it to A's bottom point.
    //Point offset(min_a - max_b);
    Point offset; // in SVGNest this is startOffset or startPoint
    // TODO: If we're looking for interior NFP:
    // offset = search_start_point(A, B, inside = true);
    // else: offset is the min_a point
    offset = min_a-max_b;
    while(true){ // iterate over all possible starting points that are not covered in the current nfp

        // We're creating the NFP with the first point in the B polygon
        nfp.append(B.points[0]+offset);

        // This will be moving with B and we'll check if it returns to start point
        // then we're finished with the NFP from the specified start point
        Point reference(offset);
        int counter = 0; // Used for preventing infinite loop


        while(counter < 10*(A.points.size() + B.points.size())) {
            // This vector is used to hold the type of the pair of edges
            std::vector<int> type;
            // This vector holds the indices of the pair of edges which are touching each other in polygons A and B
            Points edges_indices;

            // First we get the touching edges and their type
            /* We have three cases here:
            * 1) Both edges touch at a single vertex. ( I think this single vertex belongs to each polygon )
            * 2) A vertex of an edge in B touches the middle of an edge in A.
            * 3) A vertex of an edge in A touches the middle of an edge in B.
            * These determine how we're gonna derive the translation vectors.
            * */
            for(int i = 0; i < A.points.size(); ++i){
                // this is to close the loop to connect last vertex to the first one creating the last edge
                int next_i = i == (A.points.size()-1) ? 0 : i+1;
                for(int j = 0; j < B.points.size(); ++j){
                    int next_j = j == (B.points.size()-1)? 0 : j+1;
//                    Point b1(B.points[j]+offset);
//                    Point b2(B.points[next_j]+offset);
                    if(almost_equal(A.points[i],B.points[j]+offset)){
                        // First case: both polygons share a common vertex at either the start or the end of the current edges
                        type.push_back(0);
                        edges_indices.push_back(Point(i,j));
                    }else if(almost_equal((B.points[j]+offset).distance_to(Line(A.points[i],A.points[next_i])),0)){
                        // Second case: vertex of B's edge is in the middle of A's edge
                        type.push_back(1);
                        edges_indices.push_back(Point(next_i,j));
                    }else if(almost_equal(A.points[i].distance_to(Line(B.points[i]+offset,B.points[next_j]+offset)),0)){
                        // Second case: vertex of B's edge is in the middle of A's edge
                        type.push_back(2);
                        edges_indices.push_back(Point(i,next_j));
                    }
                }

            }

            // Generate the translation vectors
            std::vector<TranslationVector> translation_vectors;
            for(int i = 0; i < edges_indices.size(); ++i){
                A.points[edges_indices[i].x].marked = true;
                Point vertex_A = A.points[edges_indices[i].x];

                // Adjacent A vertices
                int prev_A_index = edges_indices[i].x-1;
                int next_A_index = edges_indices[i].x+1;
                // Loop back
                prev_A_index = (prev_A_index < 0) ? A.points.size()-1 : prev_A_index;
                next_A_index = (prev_A_index >= A.points.size()) ? 0 : next_A_index;

                Point prev_A = A.points[prev_A_index];
                Point next_A = A.points[next_A_index];

                Point vertex_B = B.points[edges_indices[i].y];

                int prev_B_index = edges_indices[i].y-1;
                int next_B_index = edges_indices[i].y+1;
                // Loop back
                prev_B_index = (prev_B_index < 0) ? B.points.size()-1 : prev_B_index;
                next_B_index = (prev_B_index >= B.points.size()) ? 0 : next_B_index;

                Point prev_B = B.points[prev_B_index];
                Point next_B = B.points[next_B_index];

                if(type[i] == 0){
                    TranslationVector vA1, vA2, vB1, vB2;

                    vA1.dir = Point(prev_A-vertex_A);
                    vA1.start = vertex_A;
                    vA1.end = prev_A;

                    vA2.dir = Point(next_A - vertex_A);
                    vA2.start = vertex_A;
                    vA2.end = next_A;

                    // B vectors are inverted to achieve correct sliding
                    vB1.dir = Point(vertex_B - prev_B);
                    vB1.start = prev_B;
                    vB1.end = vertex_B;

                    vB2.dir = Point(vertex_B - next_B);
                    vB2.start = next_B;
                    vB2.end = vertex_B;

                    translation_vectors.push_back(vA1);
                    translation_vectors.push_back(vA2);
                    translation_vectors.push_back(vB1);
                    translation_vectors.push_back(vB2);

                }else if(type[i] == 1){
                    // This is the second case were we use the stationary polygon's edge to get the transition vector
                    TranslationVector vA1, vA2;

                    vA1.dir = vertex_A - vertex_B + offset;
                    vA1.start = prev_A;
                    vA1.end = vertex_A;

                    // TODO: I don't think that we need this??
                    vA2.dir = prev_A - vertex_B + offset;
                    vA2.start = vertex_A;
                    vA2.end = prev_A;
                    translation_vectors.push_back(vA1);
                    translation_vectors.push_back(vA2);

                }else if(type[i] == 2){
                    TranslationVector vB1, vB2;

                    vB1.dir = vertex_A - vertex_B + offset;
                    vB1.start = prev_B;
                    vB1.end = vertex_B;

                    // TODO: We don't need this also I think?
                    vB2.dir = vertex_A - prev_B + offset;
                    vB2.start = vertex_B;
                    vB2.end = prev_B;

                    translation_vectors.push_back(vB1);
                    translation_vectors.push_back(vB2);
                }
            }
            // Reject vectors that will cause intersection
            double max_distance = 0;
            TranslationVector translate;
            for(auto & translation_vector : translation_vectors){
                // TODO: not sure what this is for?? I'll check it after I finish
                if(translation_vector.dir == Point(0,0)) {
                    continue;
                }

                // TODO: if this vector points us back to where we came from ignore it
                // cross product = 0, dot product < 0
                // prev_vector , translation_vectors[i]

                // Calculate the maximum distance we can slide alongside each vector
                double dist = polygon_slide_distance(A, B, offset, translation_vector );
                double vecd2 = translation_vector.dir.x * translation_vector.dir.x +
                        translation_vector.dir.y * translation_vector.dir.y;
                if(dist == -1 || dist*dist > vecd2){
                    dist = sqrt(vecd2);
                }
                // TODO: I think the first condition seems redundant. Check it later
                if( dist !=-1 && dist > max_distance ){
                    max_distance = dist;
                    translate = translation_vector;
                }
            }
            // polygon_slide_distance( A, B, TrasnationVector );
            // Get the maximum translation vector and update the current offset to translate B by that
        }



        // If no more new start_offset
        break;
    }

    return Polygon();
}

bool within_distance(Point p1, Point p2, double distance) {
    double dx = p1.x - p2.x;
    double dy = p1.y - p2.y;
    return ((dx*dx + dy*dy)< distance*distance);
}
bool almost_equal(double x, double y, double tolerance){
    return abs(x-y)<=tolerance;
}
bool almost_equal(Point a, Point b, double tolerance) {
    return ((a.x-b.x <= tolerance) && (a.y-b.y <= tolerance));
}




        void
MedialAxis::build(ThickPolylines* polylines)
{
    construct_voronoi(this->lines.begin(), this->lines.end(), &this->vd);
    
    /*
    // DEBUG: dump all Voronoi edges
    {
        SVG svg("voronoi.svg");
        svg.draw(*this->expolygon);
        for (VD::const_edge_iterator edge = this->vd.edges().begin(); edge != this->vd.edges().end(); ++edge) {
            if (edge->is_infinite()) continue;
            
            ThickPolyline polyline;
            polyline.points.push_back(Point( edge->vertex0()->x(), edge->vertex0()->y() ));
            polyline.points.push_back(Point( edge->vertex1()->x(), edge->vertex1()->y() ));
            polyline.width.push_back(this->max_width);
            polyline.width.push_back(this->max_width);
            polylines->push_back(polyline);
            
            svg.draw(polyline);
        }
        svg.Close();
        return;
    }
    */
    
    // collect valid edges (i.e. prune those not belonging to MAT)
    // note: this keeps twins, so it inserts twice the number of the valid edges
    this->valid_edges.clear();
    {
        std::set<const VD::edge_type*> seen_edges;
        for (VD::const_edge_iterator edge = this->vd.edges().begin(); edge != this->vd.edges().end(); ++edge) {
            // if we only process segments representing closed loops, none if the
            // infinite edges (if any) would be part of our MAT anyway
            if (edge->is_secondary() || edge->is_infinite()) continue;
        
            // don't re-validate twins
            if (seen_edges.find(&*edge) != seen_edges.end()) continue;  // TODO: is this needed?
            seen_edges.insert(&*edge);
            seen_edges.insert(edge->twin());
            
            if (!this->validate_edge(&*edge)) continue;
            this->valid_edges.insert(&*edge);
            this->valid_edges.insert(edge->twin());
        }
    }
    this->edges = this->valid_edges;
    
    // iterate through the valid edges to build polylines
    while (!this->edges.empty()) {
        const VD::edge_type* edge = *this->edges.begin();
        
        // start a polyline
        ThickPolyline polyline;
        polyline.points.push_back(Point( edge->vertex0()->x(), edge->vertex0()->y() ));
        polyline.points.push_back(Point( edge->vertex1()->x(), edge->vertex1()->y() ));
        polyline.width.push_back(this->thickness[edge].first);
        polyline.width.push_back(this->thickness[edge].second);
        
        // remove this edge and its twin from the available edges
        (void)this->edges.erase(edge);
        (void)this->edges.erase(edge->twin());
        
        // get next points
        this->process_edge_neighbors(edge, &polyline);
        
        // get previous points
        {
            ThickPolyline rpolyline;
            this->process_edge_neighbors(edge->twin(), &rpolyline);
            polyline.points.insert(polyline.points.begin(), rpolyline.points.rbegin(), rpolyline.points.rend());
            polyline.width.insert(polyline.width.begin(), rpolyline.width.rbegin(), rpolyline.width.rend());
            polyline.endpoints.first = rpolyline.endpoints.second;
        }
        
        assert(polyline.width.size() == polyline.points.size()*2 - 2);
        
        // prevent loop endpoints from being extended
        if (polyline.first_point().coincides_with(polyline.last_point())) {
            polyline.endpoints.first = false;
            polyline.endpoints.second = false;
        }
        
        // append polyline to result
        polylines->push_back(polyline);
    }
}

void
MedialAxis::build(Polylines* polylines)
{
    ThickPolylines tp;
    this->build(&tp);
    polylines->insert(polylines->end(), tp.begin(), tp.end());
}

void
MedialAxis::process_edge_neighbors(const VD::edge_type* edge, ThickPolyline* polyline)
{
    while (true) {
        // Since rot_next() works on the edge starting point but we want
        // to find neighbors on the ending point, we just swap edge with
        // its twin.
        const VD::edge_type* twin = edge->twin();
    
        // count neighbors for this edge
        std::vector<const VD::edge_type*> neighbors;
        for (const VD::edge_type* neighbor = twin->rot_next(); neighbor != twin;
            neighbor = neighbor->rot_next()) {
            if (this->valid_edges.count(neighbor) > 0) neighbors.push_back(neighbor);
        }
    
        // if we have a single neighbor then we can continue recursively
        if (neighbors.size() == 1) {
            const VD::edge_type* neighbor = neighbors.front();
            
            // break if this is a closed loop
            if (this->edges.count(neighbor) == 0) return;
            
            Point new_point(neighbor->vertex1()->x(), neighbor->vertex1()->y());
            polyline->points.push_back(new_point);
            polyline->width.push_back(this->thickness[neighbor].first);
            polyline->width.push_back(this->thickness[neighbor].second);
            (void)this->edges.erase(neighbor);
            (void)this->edges.erase(neighbor->twin());
            edge = neighbor;
        } else if (neighbors.size() == 0) {
            polyline->endpoints.second = true;
            return;
        } else {
            // T-shaped or star-shaped joint
            return;
        }
    }
}

bool
MedialAxis::validate_edge(const VD::edge_type* edge)
{
    // prevent overflows and detect almost-infinite edges
    if (std::abs(edge->vertex0()->x()) > (double)MAX_COORD
     || std::abs(edge->vertex0()->y()) > (double)MAX_COORD
     || std::abs(edge->vertex1()->x()) > (double)MAX_COORD
     || std::abs(edge->vertex1()->y()) > (double)MAX_COORD)
        return false;
    
    // construct the line representing this edge of the Voronoi diagram
    const Line line(
        Point( edge->vertex0()->x(), edge->vertex0()->y() ),
        Point( edge->vertex1()->x(), edge->vertex1()->y() )
    );
    
    // discard edge if it lies outside the supplied shape
    // this could maybe be optimized (checking inclusion of the endpoints
    // might give false positives as they might belong to the contour itself)
    if (this->expolygon != NULL) {
        if (line.a.coincides_with(line.b)) {
            // in this case, contains(line) returns a false positive
            if (!this->expolygon->contains(line.a)) return false;
        } else {
            if (!this->expolygon->contains(line)) return false;
        }
    }
    
    // retrieve the original line segments which generated the edge we're checking
    const VD::cell_type* cell_l = edge->cell();
    const VD::cell_type* cell_r = edge->twin()->cell();
    const Line &segment_l = this->retrieve_segment(cell_l);
    const Line &segment_r = this->retrieve_segment(cell_r);
    
    /*
    SVG svg("edge.svg");
    svg.draw(*this->expolygon);
    svg.draw(line);
    svg.draw(segment_l, "red");
    svg.draw(segment_r, "blue");
    svg.Close();
    */
    
    /*  Calculate thickness of the cross-section at both the endpoints of this edge.
        Our Voronoi edge is part of a CCW sequence going around its Voronoi cell 
        located on the left side. (segment_l).
        This edge's twin goes around segment_r. Thus, segment_r is 
        oriented in the same direction as our main edge, and segment_l is oriented
        in the same direction as our twin edge.
        We used to only consider the (half-)distances to segment_r, and that works
        whenever segment_l and segment_r are almost specular and facing. However, 
        at curves they are staggered and they only face for a very little length
        (our very short edge represents such visibility).
        Both w0 and w1 can be calculated either towards cell_l or cell_r with equal
        results by Voronoi definition.
        When cell_l or cell_r don't refer to the segment but only to an endpoint, we
        calculate the distance to that endpoint instead.  */
    
    coordf_t w0 = cell_r->contains_segment()
        ? line.a.distance_to(segment_r)*2
        : line.a.distance_to(this->retrieve_endpoint(cell_r))*2;
    
    coordf_t w1 = cell_l->contains_segment()
        ? line.b.distance_to(segment_l)*2
        : line.b.distance_to(this->retrieve_endpoint(cell_l))*2;
    
    if (cell_l->contains_segment() && cell_r->contains_segment()) {
        // calculate the relative angle between the two boundary segments
        double angle = fabs(segment_r.orientation() - segment_l.orientation());
        if (angle > PI) angle = 2*PI - angle;
        assert(angle >= 0 && angle <= PI);
        
        // fabs(angle) ranges from 0 (collinear, same direction) to PI (collinear, opposite direction)
        // we're interested only in segments close to the second case (facing segments)
        // so we allow some tolerance.
        // this filter ensures that we're dealing with a narrow/oriented area (longer than thick)
        // we don't run it on edges not generated by two segments (thus generated by one segment
        // and the endpoint of another segment), since their orientation would not be meaningful
        if (PI - angle > PI/8) {
            // angle is not narrow enough
            
            // only apply this filter to segments that are not too short otherwise their 
            // angle could possibly be not meaningful
            if (w0 < SCALED_EPSILON || w1 < SCALED_EPSILON || line.length() >= this->min_width)
                return false;
        }
    } else {
        if (w0 < SCALED_EPSILON || w1 < SCALED_EPSILON)
            return false;
    }
    
    if (w0 < this->min_width && w1 < this->min_width)
        return false;
    
    if (w0 > this->max_width && w1 > this->max_width)
        return false;
    
    this->thickness[edge]         = std::make_pair(w0, w1);
    this->thickness[edge->twin()] = std::make_pair(w1, w0);
    
    return true;
}

const Line&
MedialAxis::retrieve_segment(const VD::cell_type* cell) const
{
    return this->lines[cell->source_index()];
}

const Point&
MedialAxis::retrieve_endpoint(const VD::cell_type* cell) const
{
    const Line& line = this->retrieve_segment(cell);
    if (cell->source_category() == SOURCE_CATEGORY_SEGMENT_START_POINT) {
        return line.a;
    } else {
        return line.b;
    }
}

} }
