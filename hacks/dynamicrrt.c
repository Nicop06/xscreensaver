/*  dynamicrrt, Copyright (c) 2015 Nicolas Porcel
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

#define NB_COLORS          4
#define COLOR_LINES        0
#define COLOR_OTHER_LINES  1
#define COLOR_ROBOT        2
#define COLOR_OBSTACLES    3

typedef struct {
  float x;
  float y;
} Point;

typedef struct {
  Point pos;
  Point v;
  float radius;
} Obstacle;

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
  struct Node *prev;
  List neighbors;
} Node;

typedef struct {
  List nodes;
  int size;
} Tree;

struct state {
  Display *dpy;
  Window window;
  XWindowAttributes wa;

  Pixmap b, ba, bb;

#ifdef HAVE_DOUBLE_BUFFER_EXTENSION
  XdbeBackBuffer backb;
#endif

  long delay;              /*  usecs to wait between updates.  */

  unsigned int scrWidth, scrHeight;
  int mapWidth, mapHeight;
  GC gcDraw, gcClear;

  Bool dbuf;

  XGCValues gcv;
  Colormap cmap;
  XColor *colors;
  int nbcolors;

  int nbobstacles;
  float obstacle_radius;
  float robot_radius;
  float obstacle_speed;
  float robot_speed;
  float offset;

  float goal_action;
  float connect_action;

  Obstacle* obstacles;
  Point robot;
  Point goal;

  List trees;
  Tree *current_tree;
  int nbtrees;
  int max_trees;
  int max_steps;

  List path;
  Node *goal_node;
  Tree *goal_tree;
};

/*
 * ----------------------------------------
 *  LIST
 * ----------------------------------------
 */

static Item* list_insert_after(List *list, Item *prev_item, void* val)
{
  Item *item = malloc(sizeof(Item));
  item->val = val;
  item->previous = prev_item;

  if (prev_item) {
    item->next = prev_item->next;
    prev_item->next = item;

    if (prev_item->next)
      prev_item->next->previous = item;
  } else {
    item->next = *list;

    if (*list)
      (*list)->previous = item;

    *list = item;
  }

  return item;
}

static Item* list_insert(List *list, void* val)
{
  return list_insert_after(list, NULL, val);
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
  void *val;
  while (*list != NULL) {
    val = list_pop(list);
    if (val_delete)
      val_delete(val);
  }
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
  new_node->neighbors = NULL;

  if (tree_node) {
    list_insert(&new_node->neighbors, tree_node);
    list_insert(&tree_node->neighbors, new_node);
  }

  list_insert(&tree->nodes, new_node);
  ++tree->size;
  return new_node;
}

/*
 * ----------------------------------------
 *  COLLISION
 * ----------------------------------------
 */

static float vector_cross(Point p1, Point p2)
{
  return p1.x * p2.y - p1.y * p2.x;
}

static float vector_dot(Point p1, Point p2)
{
  return p1.x * p2.x + p1.y * p2.y;
}

static float vector_norm(Point p)
{
  return vector_dot(p, p);
}

static Point vector(Point p1, Point p2)
{
  Point vect;
  vect.x = p2.x - p1.x;
  vect.y = p2.y - p1.y;
  return vect;
}

static float points_distance(Point p1, Point p2)
{
  return vector_norm(vector(p1, p2));
}

static bool point_inside_circle(Point c_center, float radius, Point p)
{
  return points_distance(c_center, p) < radius * radius;
}

static bool circle_line_collision(Point c_center, float radius, Point line_p1, Point line_p2)
{
  Point v_p1p2 = vector(line_p1, line_p2);
  Point v_p1c = vector(line_p1, c_center);

  /*  Check that the projection of c on vect(p1, p2) is between p1 and p2 */
  float p1p2 = vector_norm(v_p1p2);
  float p1c = vector_dot(v_p1p2, v_p1c);

  if (p1c < 0 || p1c > p1p2) {
    /*  Check if any point of the line is inside the circle */
    return point_inside_circle(c_center, radius, line_p1)
           || point_inside_circle(c_center, radius, line_p2);
  }

  /*
   * Check if the distance from the center of circle to vect(p1, p2) is
   * less than the radius of the circle
   */
  return fabs(vector_cross(v_p1p2, v_p1c)) < radius * sqrt(p1p2);
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
  pos.x = random() % st->mapWidth;
  pos.y = random() % st->mapHeight;
  return pos;
}

static void rrt_insert_tree(struct state *st, Tree *new_tree)
{
  Tree *tree = NULL;
  Item *prev_i_tree = NULL;
  Item *i_tree;

  /* Insert the new tree such that the trees are sorted by size */
  for (i_tree = st->trees; i_tree != NULL; prev_i_tree = i_tree, i_tree = i_tree->next) {
    tree = i_tree->val;
    if (new_tree->size > tree->size)
      break;
  }

  if (list_search(new_tree->nodes, st->goal_node)) {
    st->goal_tree = new_tree;
  }

  list_insert_after(&st->trees, prev_i_tree, new_tree);

  /* Remove the smallest tree if the list is too big */
  if (++st->nbtrees > st->max_trees) {
    tree = list_pop(&st->trees);

    /* Do not extract the current tree */
    if (tree == st->current_tree && tree != NULL) {
      tree = list_pop(&st->trees);
      list_insert(&st->trees, st->current_tree);
    }

    /* Do not delete the current tree (holding the path) */
    if (tree != NULL) {
      --st->nbtrees;
      /* The tree containing the goal has been removed */
      if (tree == st->goal_tree) {
        st->goal_tree = NULL;
        st->goal_node = NULL;
      }
      tree_delete(tree);
    }
  }
}

static void rrt_check_path(struct state *st)
{
  Item *i_node;
  Node *node;

  if (!st->path)
    return;

  /* Check if path is conneted */
  for (i_node = st->path; i_node != NULL; i_node = i_node->next) {
    node = i_node->val;
    if (!i_node->next || !list_search(node->neighbors, i_node->next->val)) {
      /* The path is broken, delete it and remove the current tree */
      list_delete(&st->path, NULL);
      st->current_tree = NULL;
      return;
    }
  }
}

static void rrt_prune(struct state *st)
{
  Tree *tree;
  Tree *new_tree;
  Item *i_node1, *i_node2;
  Node *node1, *node2;
  bool rebuild_tree = false;

  List old_trees = st->trees;

  st->trees = NULL;
  st->nbtrees = 0;

  /* Delete nodes and edges colliding with obstacles */
  while (old_trees != NULL) {
    tree = list_pop(&old_trees);

    rebuild_tree = false;

    for (i_node1 = tree->nodes; i_node1 != NULL; i_node1 = i_node1->next) {
      node1 = i_node1->val;

      /* Delete nodes in collision */
      i_node2 = node1->neighbors;
      while (i_node2 != NULL) {
        node2 = i_node2->val;
        i_node2 = i_node2->next;
        if (line_obstacles_collision(st->obstacles, st->nbobstacles, node1->pos, node2->pos)) {
          rebuild_tree = true;
          list_remove(&node1->neighbors, node2);
          list_remove(&node2->neighbors, node1);
        }
      }
    }

    /* Rebuild trees if cut */
    if (rebuild_tree) {
      List visited_nodes = NULL;
      Node *extracted_node, *path_node = NULL;

      /* Check if the path if connected and nullify it if not */
      if (tree == st->current_tree) {
        rrt_check_path(st);

        /* Store the first node of the path */
        if (st->path)
          path_node = st->path->val;
      }

      /* Prepare tree rebuilding */
      for (i_node1 = tree->nodes; i_node1 != NULL; i_node1 = i_node1->next) {
        node1 = i_node1->val;
        node1->marked = false;
      }

      while (tree->nodes != NULL) {
        new_tree = malloc(sizeof(Tree));
        new_tree->size = 0;
        new_tree->nodes = NULL;

        node1 = list_pop(&tree->nodes);
        node1->marked = true;
        list_insert(&visited_nodes, node1);

        /* Create a tree listing all the connected nodes */
        while (visited_nodes != NULL) {
          extracted_node = list_pop(&visited_nodes);
          list_insert(&new_tree->nodes, extracted_node);
          ++new_tree->size;

          /* The tree containing the path is the current tree */
          if (path_node && path_node == extracted_node) {
            st->current_tree = new_tree;
            path_node = NULL;
          }

          /* Go through the neighbors not already visited and add them to the new tree */
          for (i_node1 = extracted_node->neighbors; i_node1 != NULL; i_node1 = i_node1->next) {
            node1 = i_node1->val;
            if (!node1->marked) {
              list_remove(&tree->nodes, node1);
              node1->marked = true;
              list_insert(&visited_nodes, node1);
            }
          }
        }

        /* Add the new tree to tree list */
        rrt_insert_tree(st, new_tree);
      }

      free(tree);
    } else {
      rrt_insert_tree(st, tree);
    }
  }
}

static Node* rrt_nearest_neighbor(Tree *tree, Point pos, float *distance)
{
  Item *i_node;
  Node *node, *nearest_node = NULL;
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

  if (action < st->goal_action) {
    /* Try to connect to the goal */
    Node *nearest_node = rrt_nearest_neighbor(st->current_tree, st->goal, NULL);
    if (nearest_node && !line_obstacles_collision(st->obstacles, st->nbobstacles, nearest_node->pos, st->goal)) {
      /* Keep track of the tree containing the goal node */
      st->goal_node = tree_connect_point(st->current_tree, nearest_node, st->goal);
      st->goal_tree = st->current_tree;
      return true;
    }
  } else if (action < st->connect_action && st->nbtrees > 1) {
    /* Tree to connect to the current tree */
    Item *i_tree, *i_node;
    Node *node, *cur_node, *nearest_node = NULL, *cur_nearest_node = NULL;
    Tree *tree;
    float dist, min_dist = -1.0;

    /* Select and extract a random non-current tree */
    int tree_to_connect = random() % st->nbtrees - 1;
    for (i_tree = st->trees; i_tree != NULL && tree_to_connect > 0; i_tree = i_tree->next) {
      if (i_tree->val != st->current_tree)
        --tree_to_connect;
    }

    tree = list_extract(&st->trees, i_tree);

    /* Find the nearest nodes between the current and the select tree */
    for (i_node = st->current_tree->nodes; i_node != NULL; i_node = i_node->next) {
      cur_node = i_node->val;
      node = rrt_nearest_neighbor(tree, cur_node->pos, &dist);
      if (dist < min_dist || min_dist < 0.0) {
        min_dist = dist;
        nearest_node = node;
        cur_nearest_node = cur_node;
      }
    }

    /* Connect the trees */
    if (!line_obstacles_collision(st->obstacles, st->nbobstacles, nearest_node->pos, cur_nearest_node->pos)) {
      list_insert(&cur_nearest_node->neighbors, nearest_node);
      list_insert(&nearest_node->neighbors, cur_nearest_node);
      list_concatenate(&st->current_tree->nodes, tree->nodes);
      st->current_tree->size += tree->size;
      --st->nbtrees;

      /* The tree containing the goal changed */
      if (tree == st->goal_tree)
        st->goal_tree = st->current_tree;

      free(tree);

      if (st->current_tree == st->goal_tree)
        return true;
    }
  } else {
    Point new_pos = rrt_random_point(st);
    Node *nearest_node = rrt_nearest_neighbor(st->current_tree, new_pos, NULL);
    if (nearest_node && !line_obstacles_collision(st->obstacles, st->nbobstacles, nearest_node->pos, new_pos))
      tree_connect_point(st->current_tree, nearest_node, new_pos);
  }

  return false;
}

static void rrt_compute_path(struct state *st)
{
  Item *i_node, *i_next_node = NULL, *i_tree;
  Node *node, *start_node = NULL, *cur_node = NULL;
  Tree *tree = NULL;
  float dist, min_dist = -1.0;
  List opened_nodes = NULL;

  /* We already have a valid path */
  if (st->path)
    return;

  /* Find the nearest tree to the robot */
  for (i_tree = st->trees; i_tree != NULL; i_tree = i_tree->next) {
    node = rrt_nearest_neighbor(i_tree->val, st->robot, &dist);
    if (dist < min_dist || min_dist < 0.0) {
      min_dist = dist;
      start_node = node;
      tree = i_tree->val;
    }
  }

  /* Compute the current tree by trying to connect the robot to the nearest tree */
  if (tree && start_node && !line_obstacles_collision(st->obstacles, st->nbobstacles, start_node->pos, st->robot)) {
    st->current_tree = tree;
    tree_connect_point(tree, start_node, st->robot);
  } else {
    st->current_tree = malloc(sizeof(Tree));
    st->current_tree->size = 0;
    st->current_tree->nodes = NULL;
    tree_connect_point(st->current_tree, NULL, st->robot);
    list_insert(&st->trees, st->current_tree);
    ++st->nbtrees;
    return;
  }

  /*  There is no way to the goal, don't look for a path */
  if (st->goal_tree != st->current_tree)
    return;

  /*
   * Find shortest path (Dijkstra's algorithm)
   * STEP 1: Initialization
   */
  for (i_node = st->current_tree->nodes; i_node != NULL; i_node = i_node->next) {
    node = i_node->val;
    node->marked = false;
    node->prev = NULL;
    node->dist = -1.0;
  }

  list_insert(&opened_nodes, start_node);
  start_node->marked = true;
  node = NULL;

  /*
   * STEP 2: Algorithm
   */
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

  list_delete(&opened_nodes, NULL);

  /*
   * STEP 3: Compute path
   */
  if (st->goal_node && cur_node == st->goal_node) {
    for (node = st->goal_node; node != NULL; node = node->prev) {
      list_insert(&st->path, node);
    }
  }
}

static bool rrt_update(struct state *st)
{
  int i;
  Obstacle *obs;
  Node *node;
  float dist, remaining_dist = st->robot_speed;

  /* Move the obstacles */
  for (i = 0; i < st->nbobstacles; ++i) {
    obs = &st->obstacles[i];
    obs->pos.x += obs->v.x;
    obs->pos.y += obs->v.y;

    if ((obs->pos.x > st->mapWidth && obs->v.x > 0) || (obs->pos.x < 0 && obs->v.x < 0))
      obs->v.x = -obs->v.x;

    if ((obs->pos.y > st->mapHeight && obs->v.y > 0) || (obs->pos.y < 0 && obs->v.y < 0))
      obs->v.y = -obs->v.y;
  }

  /* No path, do not move the robot */
  if (!st->path)
    return false;

  /* Move the robot along the path */
  while (remaining_dist > 0 && st->path != NULL) {
    node = list_pop(&st->path);
    dist = sqrt(points_distance(st->robot, node->pos));
    if (dist < remaining_dist) {
      st->robot = node->pos;
      remaining_dist -= dist;
    } else {
      Point new_pos = vector(st->robot, node->pos);
      st->robot.x += new_pos.x * remaining_dist / dist;
      st->robot.y += new_pos.y * remaining_dist / dist;
      list_insert(&st->path, node);
      remaining_dist = 0;
    }
  }

  return !st->path;
}

static void rrt_free(struct state *st)
{
  list_delete(&st->path, NULL);
  list_delete(&st->trees, (void (*)(void*)) &tree_delete);
  free(st->obstacles);
}

static void rrt_simulation_init(struct state *st)
{
  int i;

  st->obstacles = malloc(sizeof(Obstacle) * st->nbobstacles);

  for (i = 0; i < st->nbobstacles; ++i) {
    st->obstacles[i].pos = rrt_random_point(st);
    st->obstacles[i].radius = st->obstacle_radius;
    do {
      st->obstacles[i].v.x = frand(st->obstacle_speed * 2) - st->obstacle_speed;
      st->obstacles[i].v.y = frand(st->obstacle_speed * 2) - st->obstacle_speed;
    } while (vector_norm(st->obstacles[i].v) < st->obstacle_speed * st->obstacle_speed / 2);
  }

  st->robot.x = 0.0;
  st->robot.y = 0.0;

  st->goal.x = st->mapWidth;
  st->goal.y = st->mapHeight;

  st->trees = NULL;
  st->current_tree = NULL;
  st->nbtrees = 0;

  st->path = NULL;
  st->goal_node = NULL;
  st->goal_tree = NULL;
}

static void rrt_restart(struct state *st)
{
  rrt_free(st);
  rrt_simulation_init(st);
}

static void* dynamicrrt_init(Display *dpy, Window win)
{
  struct state *st = (struct state *) calloc(1, sizeof(*st));

  st->dpy = dpy;
  st->window = win;

  XGetWindowAttributes(st->dpy, st->window, &st->wa);

  st->nbcolors = NB_COLORS;
  st->colors = (XColor *) malloc(sizeof(*st->colors) * (st->nbcolors+1));
  make_random_colormap(st->wa.screen, st->wa.visual, st->wa.colormap, st->colors, &st->nbcolors, True, True, 0, True);

  st->delay = get_integer_resource(st->dpy, "delay", "Integer");
  st->nbobstacles = get_integer_resource(st->dpy, "obstacles", "Integer");
  st->obstacle_radius = get_float_resource(st->dpy, "obstacleradius", "Float");
  st->robot_radius = get_float_resource(st->dpy, "robotradius", "Float");
  st->obstacle_speed = get_float_resource(st->dpy, "obstaclespeed", "Float");
  st->robot_speed = get_float_resource(st->dpy, "robotspeed", "Float");
  st->max_trees = get_integer_resource(st->dpy, "maxtrees", "Integer");
  st->max_steps = get_integer_resource(st->dpy, "maxsteps", "Integer");
  st->goal_action = get_float_resource(st->dpy, "obstacleradius", "Float");
  st->robot_radius = get_float_resource(st->dpy, "robotradius", "Float");

  if (st->goal_action < 0 || st->goal_action > 1)
    st->goal_action = 0.4;

  if (st->connect_action < 0 || st->connect_action + st->goal_action > 1)
    st->connect_action = 0.4;

  st->offset = st->obstacle_radius;

  st->dbuf = True;

# ifdef HAVE_COCOA
  st->dbuf = False;
# endif

  st->b = st->ba = st->bb = 0;

#ifdef HAVE_DOUBLE_BUFFER_EXTENSION
  st->b = st->backb = xdbe_get_backbuffer(st->dpy, st->window, XdbeUndefined);
#endif

  st->scrWidth = st->wa.width;
  st->scrHeight = st->wa.height;
  st->mapWidth = st->wa.width - 2 * st->offset;
  st->mapHeight = st->wa.height - 2 * st->offset;
  st->cmap = st->wa.colormap;
  st->gcDraw = XCreateGC(st->dpy, st->window, 0, &st->gcv);
  st->gcv.foreground = get_pixel_resource(st->dpy, st->cmap, "background", "Background");
  st->gcClear = XCreateGC(st->dpy, st->window, GCForeground, &st->gcv);

  if (st->dbuf) {
    if (!st->b) {
      st->ba = XCreatePixmap(st->dpy, st->window, st->scrWidth, st->scrHeight, st->wa.depth);
      st->bb = XCreatePixmap(st->dpy, st->window, st->scrWidth, st->scrHeight, st->wa.depth);
      st->b = st->ba;
    }
  } else {
    st->b = st->window;
  }

  if (st->ba)
    XFillRectangle(st->dpy, st->ba, st->gcClear, 0, 0, st->scrWidth, st->scrHeight);

  if (st->bb)
    XFillRectangle(st->dpy, st->bb, st->gcClear, 0, 0, st->scrWidth, st->scrHeight);

  XClearWindow(st->dpy, st->window);

  rrt_simulation_init(st);

  return st;
}

static void dynamicrrt_free(Display *dpy, Window window, void *closure);

static unsigned long dynamicrrt_draw(Display *dpy, Window window, void *closure)
{
  int i;
  Obstacle *obs;
  Tree *tree;
  Node *node1, *node2;
  Item *i_tree, *i_node1, *i_node2;
  bool arrived = false;
  struct state *st = (struct state*) closure;

  /* Prune nodes for collision */
  rrt_prune(st);

  /* Compute a path */
  rrt_compute_path(st);

  /* No path, try to add nodes and connect trees */
  if (!st->path) {
    for (i = 0; i < st->max_steps; ++i) {
      /* Try to compute a new path if we rreachedeached the goal */
      if (rrt_extend_trees(st)) {
        rrt_compute_path(st);
        break;
      }
    }
  }

  /* If their is a path, update the position of the robot */
  arrived = rrt_update(st);

  /*
   * -------------------------
   *  DRAWING
   * -------------------------
   */

  /* Clear everything */
  XFillRectangle(st->dpy, st->b, st->gcClear, 0, 0, st->scrWidth, st->scrHeight);

  /* Trees */
  for (i_tree = st->trees; i_tree != NULL; i_tree = i_tree->next) {
    tree = i_tree->val;
    XSetForeground(st->dpy, st->gcDraw, st->colors[tree == st->current_tree ? COLOR_LINES : COLOR_OTHER_LINES].pixel);
    for (i_node1 = tree->nodes; i_node1 != NULL; i_node1 = i_node1->next) {
      node1 = i_node1->val;
      for (i_node2 = node1->neighbors; i_node2 != NULL; i_node2 = i_node2->next) {
        node2 = i_node2->val;
        XDrawLine(st->dpy, st->b, st->gcDraw, node1->pos.x + st->offset, node1->pos.y + st->offset, node2->pos.x + st->offset, node2->pos.y + st->offset);
      }
    }
  }

  /* Robot */
  XSetForeground(st->dpy, st->gcDraw, st->colors[COLOR_ROBOT].pixel);
  XFillArc(st->dpy, st->b, st->gcDraw, st->robot.x - st->robot_radius + st->offset, st->robot.y - st->robot_radius + st->offset,
      st->robot_radius * 2, st->robot_radius * 2, 0, 360 * 64);

  /* Obstacle */
  XSetForeground(st->dpy, st->gcDraw, st->colors[COLOR_OBSTACLES].pixel);
  for (i = 0; i < st->nbobstacles; ++i) {
    obs = &st->obstacles[i];
    XFillArc(st->dpy, st->b, st->gcDraw, obs->pos.x - obs->radius + st->offset, obs->pos.y - obs->radius + st->offset,
        obs->radius * 2, obs->radius * 2, 0, 360 * 64);
  }

  /* Swip buffers */
#ifdef HAVE_DOUBLE_BUFFER_EXTENSION
  if (st->backb) {
    XdbeSwapInfo info[1];
    info[0].swap_window = st->window;
    info[0].swap_action = XdbeUndefined;
    XdbeSwapBuffers(st->dpy, info, 1);
  }
  else
#endif
    if (st->dbuf)	{
      XCopyArea(st->dpy, st->b, st->window, st->gcClear, 0, 0, st->scrWidth, st->scrHeight, 0, 0);
      st->b = (st->b == st->ba ? st->bb : st->ba);
    }

  /* We arrived, reset the screen */
  if (arrived) {
    rrt_free(st);
    rrt_simulation_init(st);
  }

  return st->delay;
}

static void dynamicrrt_reshape(Display *dpy, Window window, void *closure, unsigned int w, unsigned int h)
{
  struct state *st = (struct state *) closure;

  if (w != st->scrWidth || h != st->scrHeight) {
    st->scrWidth = w;
    st->scrHeight = h;
    st->mapWidth = w - 2 * st->offset;
    st->mapHeight = h - 2 * st->offset;
    rrt_restart(st);
  } 
}

static Bool dynamicrrt_event (Display *dpy, Window window, void *closure, XEvent *event)
{
  return False;
}

static void dynamicrrt_free(Display *dpy, Window window, void *closure)
{
  struct state *st = (struct state *) closure;
  rrt_free(st);
  XFreeGC(st->dpy, st->gcDraw);
  XFreeGC(st->dpy, st->gcClear);
  free(st->colors);
  free(st);
}




static const char *dynamicrrt_defaults [] = {
  ".background: black",
  "*obstacleradius: 40",
  "*robotradius: 10",
  "*obstaclespeed: 6.0",
  "*robotspeed: 6.0",
  "*maxtrees: 5",
  "*maxsteps: 10",
  "*delay: 20000",
  "*obstacles: 10",
  "*goalacction: 0.4",
  "*connectaction: 0.4",
#ifdef HAVE_DOUBLE_BUFFER_EXTENSION
  "*useDBE: True",
#endif
  0
};

static XrmOptionDescRec dynamicrrt_options [] = {
  { "-delay"         , ".delay"         , XrmoptionSepArg, 0 },
  { "-obstacleradius", ".obstacleradius", XrmoptionSepArg, 0 },
  { "-robotradius"   , ".robotradius"   , XrmoptionSepArg, 0 },
  { "-obstaclespeed" , ".obstaclespeed" , XrmoptionSepArg, 0 },
  { "-robotspeed"    , ".robotspeed"    , XrmoptionSepArg, 0 },
  { "-maxtrees"      , ".maxtrees"      , XrmoptionSepArg, 0 },
  { "-maxsteps"      , ".maxsteps"      , XrmoptionSepArg, 0 },
  { "-obstacles"     , ".obstacles"     , XrmoptionSepArg, 0 },
  { "-goalaction"    , ".goalaction"    , XrmoptionSepArg, 0 },
  { "-connectaction" , ".connectaction" , XrmoptionSepArg, 0 },
  { 0                , 0                , 0              , 0 }
};


XSCREENSAVER_MODULE ("DynamicRRT", dynamicrrt)
