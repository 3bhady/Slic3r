#ifndef slic3r_Geometry_hpp_
#define slic3r_Geometry_hpp_

#include "libslic3r.h"
#include "BoundingBox.hpp"
#include "ExPolygon.hpp"
#include "Polygon.hpp"
#include "Polyline.hpp"

#include "boost/polygon/voronoi.hpp"
using boost::polygon::voronoi_builder;
using boost::polygon::voronoi_diagram;

namespace Slic3r { namespace Geometry {

// Given some points this function returns the bounding convex hull for these points
Polygon convex_hull(Points points);

// Given vector of polygons this function returns the convex hull for all the points in these polygons combined
Polygon convex_hull(const Polygons &polygons);

// Returns a NFP for the two polygons A and B
// A is the stationary polygon and
// B is the orbiting polygon
Polygon no_fit_polygon(Polygon A, Polygon B);


Polygon inner_fit_polygon(Polygon A, Polygon B);


// For convex shapes only
// Returns a NFP for the two polygons A and B
// A is the stationary polygon and
// B is the orbiting polygon
Polygon no_fit_polygon_convex(Polygon A, Polygon B, bool inside = false);

// Returns true if the two arguments are almost equal with tolerance due to floating point accuracy
bool almost_equal(Point a, Point b, double tolerance=10e-8);
bool almost_equal(double x, double y, double tolerance = 10e-8);

struct TranslationVector{
    Pointf dir, start, end;
    TranslationVector(){
        dir = start = end = Pointf(-1,-1);
    }
    Pointf normalize(){
        // TODO: could we use normalize from point her?? return dir.normalize()
        if(almost_equal(dir.x*dir.x + dir.y*dir.y, 1)){
            return Pointf(dir.x, dir.y);
        }
        double len = sqrt(dir.x*dir.x + dir.y*dir.y);
        double inverse = 1/len;
        return Pointf(dir.x*inverse, dir.y*inverse);
    }
};

double polygon_slide_distance(Polygon A, Polygon B, Point offset, TranslationVector translationVector);
double segment_distance( Point A, Point B, Point E, Point F, Point direction );
double point_distance( Point p, Point s1, Point s2, Pointf normal, bool infinite = false );
void chained_path(const Points &points, std::vector<Points::size_type> &retval, Point start_near);
void chained_path(const Points &points, std::vector<Points::size_type> &retval);
template<class T> void chained_path_items(Points &points, T &items, T &retval);
bool directions_parallel(double angle1, double angle2, double max_diff = 0);
template<class T> bool contains(const std::vector<T> &vector, const Point &point);
template<class T> double area(const std::vector<T> &vector);
double rad2deg(double angle);
double rad2deg_dir(double angle);
double deg2rad(double angle);

// Returns true if the two points are within the given distance
bool within_distance(Point p1, Point p2, double distance);

/// Find the center of the circle corresponding to the vector of Points as an arc.
Point circle_taubin_newton(const Points& input, size_t cycles = 20);
Point circle_taubin_newton(const Points::const_iterator& input_start, const Points::const_iterator& input_end, size_t cycles = 20);

/// Find the center of the circle corresponding to the vector of Pointfs as an arc.
Pointf circle_taubin_newton(const Pointfs& input, size_t cycles = 20);
Pointf circle_taubin_newton(const Pointfs::const_iterator& input_start, const Pointfs::const_iterator& input_end, size_t cycles = 20);

/// Epsilon value
// FIXME: this is a duplicate from libslic3r.h
constexpr double epsilon { 1e-4 };
constexpr coord_t scaled_epsilon { static_cast<coord_t>(epsilon / SCALING_FACTOR) };

double linint(double value, double oldmin, double oldmax, double newmin, double newmax);
bool arrange(
    // input
    size_t num_parts, const Pointf &part_size, coordf_t gap, const BoundingBoxf* bed_bounding_box, 
    // output
    Pointfs &positions);

class MedialAxis {
    public:
    Lines lines;
    const ExPolygon* expolygon;
    double max_width;
    double min_width;
    MedialAxis(double _max_width, double _min_width, const ExPolygon* _expolygon = NULL)
        : expolygon(_expolygon), max_width(_max_width), min_width(_min_width) {};
    void build(ThickPolylines* polylines);
    void build(Polylines* polylines);
    
    private:
    typedef voronoi_diagram<double> VD;
    VD vd;
    std::set<const VD::edge_type*> edges, valid_edges;
    std::map<const VD::edge_type*, std::pair<coordf_t,coordf_t> > thickness;
    void process_edge_neighbors(const VD::edge_type* edge, ThickPolyline* polyline);
    bool validate_edge(const VD::edge_type* edge);
    const Line& retrieve_segment(const VD::cell_type* cell) const;
    const Point& retrieve_endpoint(const VD::cell_type* cell) const;
};

} }

#endif
