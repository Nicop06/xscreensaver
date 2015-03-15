/* dynamicrrt, Copyright (c) 2015 Nicolas Porcel
 *
 * Permission to use, copy, modify, distribute, and sell this software
 * and its documentation for any purpose is hereby granted without
 * fee, provided that the above copyright notice appear in all copies
 * and that both that copyright notice and this permission notice
 * appear in supporting documentation.  No representations are made
 * about the suitability of this software for any purpose. It is
 * provided "as is" without express or implied warranty.
 */

#include "screenhack.h"
#include <math.h>
#include <stdbool.h>

#ifdef HAVE_DOUBLE_BUFFER_EXTENSION
#include "xdbe.h"
#endif

#define NB_COLORS         3
#define COLOR_LINE        0
#define COLOR_ROBOT       1
#define COLOR_OBSTACLES   2

#define OFFSET            20

#define GOAL_ACTION      0.4
#define CONNECT_ACTION   0.4

typedef struct {
  float x;
  float y;
} Point;

typedef struct {
  Point pos;
  float radius;
  float v_x;
  float v_y;
} Obstacle;

typedef struct {
  Point pos;
  float speed;
} Robot;

typedef struct Item {
  void* val;
  struct Item* next;
  struct Item* previous;
} Item;

typedef Item* List;

typedef struct Node {
  Point pos;
  bool marked;
  float dist;
  Node *prev;
  List neighbors;
} Node;

typedef struct {
  List nodes;
} Tree;

struct state {
  Display *dpy;
  Window window;

  Pixmap b, ba, bb;

#ifdef HAVE_DOUBLE_BUFFER_EXTENSION
  XdbeBackBuffer backb;
#endif

  long delay;              /* usecs to wait between updates. */

  int scrWidth, scrHeight;
  int mapWidth, mapHeight;
  GC gcDraw, gcClear;

  Bool dbuf;

  XGCValues gcv;
  Colormap cmap;
  XColor *colors;
  int nbcolors;

  int nbobstacles;
  int obstacle_radius;
  int robot_radius;
  float max_speed;
  float robot_speed;

  Obstacle* obstacles;
  Robot robot;
  Point start, goal;

  List trees;
  Tree *current_tree;
  int nbtrees;
  int max_trees;

  List path;
  Node *goal_node;
};

/*
 * ----------------------------------------
 *  LIST
 * ----------------------------------------
 */

static Item* list_insert(List *list, void* val)
{
  Item *item = malloc(sizeof(Item));
  item->val = val;
  item->previous = NULL;
  item->next = *list;

  if (*list)
    (*list)->previous = item;

  *list = item;
  return item;
}

static void* list_extract(List *list, Item *item)
{
  void *val;

  if (!item)
    return NULL;

  val = item->val;

  if (item->next)
    item->next->previous = item->previous;

  if (item->previous)
    item->previous->next = item->next;

  if (item == *list)
    *list = item->next;

  free(item);
  return val;
}

static void* list_pop(List *list)
{
  return list_extract(list, *list);
}

static Item* list_search(List list, void *val)
{
  Item *item;

  for (item = list; item != NULL; item = item->next)
    if (item->val == val)
      return item;
  return NULL;
}

static void* list_remove(List *list, void *val)
{
  Item *item = list_search(*list, val);
  return list_extract(list, item);
}

static void list_delete(List *list, void (*val_delete)(void*))
{
  Item *item;
  for (item = *list; item != NULL; item = item->next) {
    if (val_delete)
      val_delete(item->val);
    free(item);
  }
  *list = NULL;
}

static void list_concatenate(List *list1, List list2)
{
  if (!list1)
    return;

  if (!*list1) {
    *list1 = list2;
  } else if (list2) {
    Item *item, *prev_item;
    for (item = *list1; item != NULL; prev_item = item,  item = item->next);
    prev_item->next = list2;
    list2->previous = prev_item;
  }
}

/*
 * ----------------------------------------
 *  TREE
 * ----------------------------------------
 */

static void tree_remove_node(Tree *tree, Item *i_node)
{
  Node *neighbor, *node = i_node->val;

  for (i_node = node->neighbors; i_node != NULL; i_node = i_node->next) {
    neighbor = i_node->val;
    if (neighbor)
      list_remove(&neighbor->neighbors, node);
  }

  list_remove(&tree->nodes, node);
  free(node);
}

static void tree_remove_edge(Node *node1, Node *node2)
{
  if (node1 && node2) {
    list_remove(&node1->neighbors, node2);
    list_remove(&node2->neighbors, node1);
  }
}

static void node_delete(void *node)
{
  if (node) {
    list_delete(&((Node*)node)->neighbors, NULL);
    free(node);
  }
}

static void tree_delete(Tree *tree)
{
  list_delete(&tree->nodes, &node_delete);
  free(tree);
}

static Node* tree_connect_point(Tree *tree, Node *tree_node, Point pos)
{
  Node *new_node = malloc(sizeof(Node));
  new_node->pos = pos;

  if (tree_node) {
    list_insert(&new_node->neighbors, tree_node);
    list_insert(&tree_node->neighbors, new_node);
  }

  list_insert(&tree->nodes, new_node);
  return new_node;
}

/*
 * ----------------------------------------
 *  COLLISION
 * ----------------------------------------
 */

static float vector_cross(Point p1, Point p2)
{
  return p1.x * p2.y - p1.y + p2.x;
}

static float vector_dot(Point p1, Point p2)
{
  return p1.x * p2.x + p1.y + p2.y;
}

static float vector_norm(Point p)
{
  return vector_dot(p, p);
}

static bool point_inside_circle(Point c_center, int radius, Point p)
{
  Point v_cp;

  // vect(c, p)
  v_cp.x = p.x - c_center.x;
  v_cp.y = p.y - c_center.y;

  return vector_norm(v_cp) < radius * radius;
}

static bool circle_line_collision(Point c_center, int radius, Point line_p1, Point line_p2)
{
  Point v_p1p2, v_p1c;

  // vect(p1, p2)
  v_p1p2.x = line_p2.x - line_p1.x;
  v_p1p2.y = line_p2.y - line_p1.y;

  // vect(p1, c)
  v_p1c.x = c_center.x - line_p1.x;
  v_p1c.y = c_center.y - line_p1.y;

  // Check that the projection of c on vect(p1, p2) is between p1 and p2
  float p1p2 = vector_norm(v_p1p2);
  float p1c = vector_dot(v_p1p2, v_p1c);

  if (p1c < 0 || p1c > p1p2) {
    // Check if any point of the line is inside the circle
    return point_inside_circle(c_center, radius, line_p1)
           || point_inside_circle(c_center, radius, line_p2);
  }

  // Check if the distance from the center of circle to vect(p1, p2) is
  // less than the radius of the circle
  return fabs(vector_cross(v_p1p2, v_p1c)) < radius * sqrt(p1p2);
}

static float points_distance(Point p1, Point p2)
{
  Point vect;
  vect.x = p2.x - p1.x;
  vect.y = p2.y - p1.y;
  return vector_norm(vect);
}

static bool line_obstacles_collision(Obstacle *obstacles, int nbobstacles, Point pos1, Point pos2)
{
  int i_obstacle;
  Obstacle *obstacle;

  for (i_obstacle = 0; i_obstacle < nbobstacles; ++i_obstacle) {
    obstacle = &obstacles[i_obstacle];
    if (circle_line_collision(obstacle->pos, obstacle->radius, pos1, pos2))
      return true;
  }

  return false;
}

/*
 * ----------------------------------------
 *  RRT
 * ----------------------------------------
 */

static Point rrt_random_point(struct state *st)
{
  Point pos;
  pos.x = random() % st->scrWidth;
  pos.y = random() % st->scrHeight;
  return pos;
}

static void rrt_prune(struct state *st)
{
  Tree *tree;
  List new_trees;
  Item *i_smallest_tree;
  Tree *new_tree;
  Item *i_node1, *i_node2;
  Node *node1, *node2;
  bool rebuild_tree;
  int tree_size, smallest_tree_size = 0;

  st->nbtrees = 0;

  // Delete nodes and edges colliding with obstacles
  while (st->trees != NULL) {
    tree = list_pop(&st->trees);

    for (i_node1 = tree->nodes; i_node1 != NULL; ) {
      node1 = i_node1->val;

      rebuild_tree = false;

      // Delete nodes in collision
      for (i_node2 = node1->neighbors; i_node2 != NULL; i_node2 = i_node2->next) {
        node2 = i_node2->val;
        if (line_obstacles_collision(st->obstacles, st->nbobstacles, node1->pos, node2->pos)) {
          rebuild_tree = true;
          tree_remove_edge(node1, node2);
        }
      }
    }

    // Rebuild trees if cut
    tree_size = 0;
    if (rebuild_tree) {
      List visited_nodes;
      Node *extracted_node;

      for (i_node1 = tree->nodes; i_node1 != NULL; i_node1 = i_node1->next) {
        node1 = i_node1->val;
        node1->marked = false;
      }

      while (tree->nodes != NULL) {
        new_tree = malloc(sizeof(Tree));
        tree_size = 0;
        list_insert(&visited_nodes, i_node1->val);
        while (visited_nodes != NULL) {
          extracted_node = list_pop(&visited_nodes);
          list_insert(&new_tree->nodes, extracted_node);
          ++tree_size;
          for (i_node2 = extracted_node->neighbors; i_node2 != NULL; i_node2 = i_node2->next) {
            node2 = i_node2->val;
            if (!node2->marked) {
              list_remove(&tree->nodes, node2);
              node2->marked = true;
              list_insert(&visited_nodes, node2);
            }
          }
        }
      }
    } else {
      new_tree = tree;
      for (i_node1 = tree->nodes; i_node1 != NULL; i_node1 = i_node1->next)
        ++tree_size;
    }

    // Only keep the biggest trees
    if (st->nbtrees >= st->max_trees) {
      if (tree_size > smallest_tree_size) {
        list_extract(&new_trees, i_smallest_tree);
        i_smallest_tree = list_insert(&new_trees, new_tree);
        smallest_tree_size = tree_size;
        ++st->nbtrees;
      }
    } else {
      Item *i_tree = list_insert(&new_trees, new_tree);
      if (!i_smallest_tree || tree_size > smallest_tree_size) {
        i_smallest_tree = i_tree;
        smallest_tree_size = tree_size;
      }
      ++st->nbtrees;
    }
  }

  st->trees = new_trees;
}

static Node* rrt_nearest_neighbor(Tree *tree, Point pos, float *distance)
{
  Item *i_node;
  Node *node, *nearest_node;
  float dist, min_dist = -1.0;

  for (i_node = tree->nodes; i_node != NULL; i_node = i_node->next) {
    node = i_node->val;
    dist = points_distance(node->pos, pos);
    if (dist < min_dist || min_dist < 0.0) {
      min_dist = dist;
      nearest_node = node;
    }
  }

  if (distance)
    *distance = min_dist;

  return nearest_node;
}

static bool rrt_extend_trees(struct state *st)
{
  float action = frand(1.0);
  if (action < GOAL_ACTION) {
    // Try to connect to goal
    Node *nearest_node = rrt_nearest_neighbor(st->current_tree, st->goal, NULL);
    if (!line_obstacles_collision(st->obstacles, st->nbobstacles, nearest_node->pos, st->goal)) {
      st->goal_node = tree_connect_point(st->current_tree, nearest_node, st->goal);
      return true;
    }
  } else if (action < CONNECT_ACTION && st->nbtrees > 1) {
    // Tree to connect to the current tree
    Item *i_tree, *i_node;
    Node *node, *cur_node, *nearest_node, *cur_nearest_node;
    Tree *tree;
    float dist, min_dist = -1.0;

    // Select and extract a random non-current tree
    int tree_to_connect = random() % st->nbtrees - 1;
    for (i_tree = st->trees; i_tree != NULL && tree_to_connect > 0; i_tree = i_tree->next) {
      if (i_tree->val != st->current_tree)
        --tree_to_connect;
    }

    tree = list_extract(&st->trees, i_tree);

    // Find the nearest node of the two trees
    for (i_node = st->current_tree->nodes; i_node != NULL; i_node = i_node->next) {
      cur_node = i_node->val;
      node = rrt_nearest_neighbor(tree, cur_node->pos, &dist);
      if (dist < min_dist || min_dist < 0.0) {
        min_dist = dist;
        nearest_node = node;
        cur_nearest_node = cur_node;
      }
    }

    // Connect the trees
    if (!line_obstacles_collision(st->obstacles, st->nbobstacles, nearest_node->pos, cur_nearest_node->pos)) {
      list_insert(&cur_nearest_node->neighbors, nearest_node);
      list_insert(&nearest_node->neighbors, cur_nearest_node);
      list_concatenate(&st->current_tree->nodes, tree->nodes);
      --st->nbtrees;
      free(tree);
      if (list_search(st->current_tree->nodes, st->goal_node))
        return true;
    }
  } else {
    Point new_pos = rrt_random_point(st);
    Node *nearest_node = rrt_nearest_neighbor(st->current_tree, new_pos, NULL);
    tree_connect_point(st->current_tree, nearest_node, new_pos);
  }

  return false;
}

static bool rrt_compute_path(struct state *st)
{
  Item *i_node, *i_next_node, *i_tree;
  Node *node, *start_node, *cur_node;
  Tree *tree;
  float dist, min_dist = -1.0;
  bool connected = st->path != NULL;
  List opened_nodes;

  // Check if path is conneted
  for (i_node = st->path; i_node != NULL; i_node = i_node->next) {
    node = i_node->val;
    if (!i_node->next || !list_search(node->neighbors, i_node->next->val)) {
      connected = false;
      break;
    }
  }

  if (connected)
    return true;

  st->path = NULL;

  // Compute current tree
  for (i_tree = st->trees; i_tree != NULL; i_tree = i_tree->next) {
    node = rrt_nearest_neighbor(i_tree->val, st->robot.pos, &dist);
    if (dist < min_dist || min_dist < 0.0) {
      min_dist = dist;
      start_node = node;
      tree = i_tree->val;
    }
  }

  if (!line_obstacles_collision(st->obstacles, st->nbobstacles, start_node->pos, st->robot.pos)) {
    st->current_tree = tree;
    tree_connect_point(tree, start_node, st->robot.pos);
  } else {
    st->current_tree = malloc(sizeof(Tree));
    start_node = tree_connect_point(st->current_tree, NULL, st->robot.pos);
    list_insert(&st->trees, st->current_tree);
  }

  if (!list_search(st->current_tree->nodes, st->goal_node))
    return false;

  // Find shortest path (Dijkstra's algorithm)
  for (i_node = st->current_tree->nodes; i_node != NULL; i_node = i_node->next) {
    node = i_node->val;
    node->marked = false;
    node->prev = NULL;
    node->dist = -1.0;
  }

  list_insert(&opened_nodes, start_node);
  start_node->marked = true;
  node = NULL;

  while (node != st->goal_node && opened_nodes != NULL) {
    min_dist = -1.0;
    for (i_node = opened_nodes; i_node != NULL; i_node = i_node->next) {
      node = i_node->val;
      if ((node->dist > 0.0 && node->dist < min_dist) || min_dist < 0.0) {
        i_next_node = i_node;
        min_dist = node->dist;
      }
    }

    cur_node = list_extract(&opened_nodes, i_next_node);
    cur_node->marked = true;

    if (cur_node == st->goal_node)
      break;

    for (i_node = cur_node->neighbors; i_node != NULL; i_node = i_node->next) {
      node = i_node->val;
      if (node->marked)
        continue;

      dist = cur_node->dist + points_distance(cur_node->pos, node->pos);
      if (dist < node->dist || node->dist < 0.0) {
        if (node->dist < 0.0)
          list_insert(&opened_nodes, node);
        node->prev = cur_node;
        node->dist = dist;
      }
    }
  }

  if (cur_node == st->goal_node) {
    for (node = st->goal_node; node != NULL; node = node->prev) {
      list_insert(&st->path, node);
    }
    return true;
  }

  return false;
}

static void rrt_simulation_init(struct state *st)
{
  int i;

  st->obstacles = malloc(sizeof(Obstacle) * st->nbobstacles);

  for (i = 0; i < st->nbobstacles; ++i) {
    st->obstacles[i].pos = rrt_random_point(st);
    st->obstacles[i].radius = st->obstacle_radius;
    st->obstacles[i].v_x = frand(st->max_speed);
    st->obstacles[i].v_y = frand(st->max_speed);
  }

  st->robot.pos.x = 0;
  st->robot.pos.y = 0;

  st->start.x = 0;
  st->start.y = 0;
  st->goal.x = st->mapWidth;
  st->goal.y = st->mapHeight;

  st->trees = NULL;
  st->current_tree = NULL;
  st->nbtrees = 0;

  st->path = NULL;
  st->goal_node = NULL;
}

static void * dynamicrrt_init(Display *dpy, Window win)
{
  struct state *st = (struct state *) calloc (1, sizeof(*st));
  XWindowAttributes wa;

  st->dpy = dpy;
  st->window = win;

  XGetWindowAttributes(st->dpy, st->window, &wa);

  st->nbcolors = NB_COLORS;
  st->colors = (XColor *) malloc(sizeof(*st->colors) * (st->nbcolors+1));
  make_random_colormap (wa.screen, wa.visual, wa.colormap, st->colors, &st->nbcolors, True, True, 0, True);

  st->delay = get_integer_resource(st->dpy, "delay", "Integer");

  st->nbobstacles = get_integer_resource(st->dpy, "obstacles", "Integer");

  if(st->nbobstacles < 0)
    st->nbobstacles = 0;

  st->obstacle_radius = get_integer_resource(st->dpy, "obstacle_radius", "Integer");

  if (st->obstacle_radius < 0)
    st->obstacle_radius = 1;

  st->robot_radius = get_integer_resource(st->dpy, "robot_radius", "Integer");

  if (st->robot_radius < 0)
    st->robot_radius = 1;

  st->max_speed = get_float_resource(st->dpy, "max_speed", "Integer");

  if (st->max_speed < 0.0)
    st->max_speed = 0.0;

  st->robot_speed = get_float_resource(st->dpy, "robot_speed", "Integer");

  if (st->robot_speed < 0.0)
    st->robot_speed = 0.0;

  st->max_trees = get_integer_resource(st->dpy, "max_trees", "Integer");

  if (st->max_trees < 1)
    st->max_trees = 1;

  st->dbuf = True;

# ifdef HAVE_COCOA
  st->dbuf = False;
# endif

  st->b = st->ba = st->bb = 0;

#ifdef HAVE_DOUBLE_BUFFER_EXTENSION
  st->b = st->backb = xdbe_get_backbuffer(st->dpy, st->window, XdbeUndefined);
#endif

  st->scrWidth = wa.width;
  st->scrHeight = wa.height;
  st->mapWidth = wa.width - 2 * OFFSET;
  st->mapHeight = wa.height - 2 * OFFSET;
  st->cmap = wa.colormap;
  st->gcDraw = XCreateGC(st->dpy, st->window, 0, &st->gcv);
  st->gcv.foreground = get_pixel_resource(st->dpy, st->cmap, "background", "Background");
  st->gcClear = XCreateGC(st->dpy, st->window, GCForeground, &st->gcv);

  if (st->dbuf) {
    if (!st->b) {
      st->ba = XCreatePixmap(st->dpy, st->window, st->scrWidth, st->scrHeight, wa.depth);
      st->bb = XCreatePixmap(st->dpy, st->window, st->scrWidth, st->scrHeight, wa.depth);
      st->b = st->ba;
    }
  } else
    st->b = st->window;

  if (st->ba) XFillRectangle(st->dpy, st->ba, st->gcClear, 0, 0, st->scrWidth, st->scrHeight);
  if (st->bb) XFillRectangle(st->dpy, st->bb, st->gcClear, 0, 0, st->scrWidth, st->scrHeight);

  rrt_simulation_init(st);

  return st;
}

static unsigned long dynamicrrt_draw(Display *dpy, Window window, void *closure)
{
}

static void dynamicrrt_reshape(Display *dpy, Window window, void *closure, unsigned int w, unsigned int h)
{
}

static Bool dynamicrrt_event (Display *dpy, Window window, void *closure, XEvent *event)
{
  return False;
}

static void dynamicrrt_free(Display *dpy, Window window, void *closure)
{
}




static const char *dynamicrrt_defaults [] = {
  ".background: black",
  "*obstacle-radius: 40",
  "*robot-radius: 10",
  "*delay: 20000",
  "*obstacles: 3",
#ifdef HAVE_DOUBLE_BUFFER_EXTENSION
  "*useDBE: True",
#endif
  0
};

static XrmOptionDescRec dynamicrrt_options [] = {
  { "-delay"          , ".delay"       , XrmoptionSepArg, 0 },
  { "-obstacle_radius", ".radius"      , XrmoptionSepArg, 0 },
  { "-robot-radius"   , ".robot_radius", XrmoptionSepArg, 0 },
  { "-max-speed"      , ".max_speed"   , XrmoptionSepArg, 0 },
  { "-robot-speed"    , ".robot_speed" , XrmoptionSepArg, 0 },
  { "-max-trees"      , ".max_trees"   , XrmoptionSepArg, 0 },
  { "-obstacles"      , ".obstacles"   , XrmoptionSepArg, 0 },
  { 0                 , 0              , 0              , 0 }
};


XSCREENSAVER_MODULE ("DynamicRRT", dynamicrrt)
