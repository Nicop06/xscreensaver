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
  List neighbors;
} Node;

typedef struct {
  List nodes;
  Node *root;
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
};

/*
 * ----------------------------------------
 *  LIST
 * ----------------------------------------
 */

static void list_insert(List *list, void* val)
{
  Item *item = malloc(sizeof(Item));
  item->val = val;
  item->previous = NULL;
  item->next = *list;

  if (*list)
    (*list)->previous = item;

  *list = item;
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

static void tree_remove_edge(Node *node1, Node *node2) {
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

static void tree_insert_node(Tree *tree, Node *node) {
  if (!tree->root)
    tree->root = node;
  list_insert(&tree->nodes, node);
}

/*
 * ----------------------------------------
 *  COLLISION
 * ----------------------------------------
 */

static float vector_cross(Point *p1, Point *p2)
{
  return p1->x * p2->y - p1->y + p2->x;
}

static float vector_dot(Point *p1, Point *p2)
{
  return p1->x * p2->x + p1->y + p2->y;
}

static float vector_norm(Point *p)
{
  return vector_dot(p, p);
}

static bool point_inside_circle(Point *c_center, int radius, Point *p) {
  Point v_cp;

  // vect(c, p)
  v_cp.x = p->x - c_center->x;
  v_cp.y = p->y - c_center->y;

  return vector_norm(&v_cp) < radius * radius;
}

static bool circle_line_collision(Point *c_center, int radius, Point *line_p1, Point *line_p2)
{
  Point v_p1p2, v_p1c;

  // vect(p1, p2)
  v_p1p2.x = line_p2->x - line_p1->x;
  v_p1p2.y = line_p2->y - line_p1->y;

  // vect(p1, c)
  v_p1c.x = c_center->x - line_p1->x;
  v_p1c.y = c_center->y - line_p1->y;

  // Check that the projection of c on vect(p1, p2) is between p1 and p2
  float p1p2 = vector_norm(&v_p1p2);
  float p1c = vector_dot(&v_p1p2, &v_p1c);

  if (p1c < 0 || p1c > p1p2) {
    // Check if any point of the line is inside the circle
    return point_inside_circle(c_center, radius, line_p1)
      || point_inside_circle(c_center, radius, line_p2);
  }

  // Check if the distance from the center of circle to vect(p1, p2) is
  // less than the radius of the circle
  return fabs(vector_cross(&v_p1p2, &v_p1c)) < radius * sqrt(p1p2);
}

/*
 * ----------------------------------------
 *  RRT
 * ----------------------------------------
 */

static void rrt_prune(List *trees, Obstacle* obstacles, int nbobstacles)
{
  Tree *tree;
  List new_trees;
  Item *i_node1, *i_node2;
  Node *node1, *node2;
  int i_obstacle;
  Obstacle *obstacle;
  bool delete_node, rebuild_tree;

  // Delete nodes and edges colliding with obstacles
  while (*trees != NULL) {
    tree = list_pop(trees);

    for (i_node1 = tree->nodes; i_node1 != NULL; ) {
      node1 = i_node1->val;
      delete_node = false;

      // Delete edges in collision
      for (i_obstacle = 0; i_obstacle < nbobstacles; ++i_obstacle) {
        obstacle = &obstacles[i_obstacle];
        if (point_inside_circle(&obstacle->pos, obstacle->radius, &node1->pos)) {
          delete_node = true;
          break;
        }
      }

      i_node2 = i_node1;
      i_node1 = i_node1->next;

      // Remove node if collision happens
      if (delete_node) {
        tree_remove_node(tree, i_node2);
        rebuild_tree = true;
        continue;
      }

      // Delete nodes in collision
      for (i_node2 = node1->neighbors; i_node2 != NULL; i_node2 = i_node2->next) {
        node2 = i_node2->val;
        for (i_obstacle = 0; i_obstacle < nbobstacles; i_obstacle++) {
          obstacle = &obstacles[i_obstacle];
          if (circle_line_collision(&obstacle->pos, obstacle->radius, &node1->pos, &node2->pos)) {
            rebuild_tree = true;
            delete_node = true;
            tree_remove_edge(node1, node2);
            break;
          }
        }
      }
    }

    // Rebuild trees if cut
    if (rebuild_tree) {
      List visited_nodes;
      Tree *new_tree;
      Node *extracted_node;

      for (i_node1 = tree->nodes; i_node1 != NULL; i_node1 = i_node1->next) {
        node1 = i_node1->val;
        node1->marked = false;
      }

      while (tree->nodes != NULL) {
        new_tree = malloc(sizeof(Tree));
        list_insert(&visited_nodes, i_node1->val);
        while (visited_nodes != NULL) {
          extracted_node = list_pop(&visited_nodes);
          tree_insert_node(new_tree, extracted_node);
          for (i_node2 = extracted_node->neighbors; i_node2 != NULL; i_node2 = i_node2->next) {
            node2 = i_node2->val;
            if (!node2->marked) {
              list_remove(&tree->nodes, node2);
              node2->marked = true;
              list_insert(&visited_nodes, node2);
            }
          }
        }
        list_insert(&new_trees, new_tree);
      }
    }
  }

  trees = &new_trees;
}

static void rrt_search()
{

}


static void simulation_init(struct state *st)
{
  int i;

  st->obstacles = malloc(sizeof(Obstacle) * st->nbobstacles);

  for (i = 0; i < st->nbobstacles; ++i) {
    st->obstacles[i].pos.x = random() % st->scrWidth;
    st->obstacles[i].pos.y = random() % st->scrHeight;
    st->obstacles[i].radius = st->obstacle_radius;
    st->obstacles[i].v_x = frand(st->max_speed);
    st->obstacles[i].v_y = frand(st->max_speed);
  }

  st->robot.pos.x = 0;
  st->robot.pos.y = 0;

  st->start.x = 0;
  st->start.y = 0;
  st->goal.x = st->scrWidth;
  st->goal.y = st->scrHeight;
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
  make_random_colormap (wa.screen, wa.visual, wa.colormap,
      st->colors, &st->nbcolors,
      True, True, 0, True);

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
  st->gcv.foreground = get_pixel_resource(st->dpy, st->cmap,
      "background", "Background");
  st->gcClear = XCreateGC(st->dpy, st->window, GCForeground, &st->gcv);

  if (st->dbuf) {
    if (!st->b) {
      st->ba = XCreatePixmap(st->dpy, st->window, st->scrWidth, st->scrHeight, wa.depth);
      st->bb = XCreatePixmap(st->dpy, st->window, st->scrWidth, st->scrHeight, wa.depth);
      st->b = st->ba;
    }
  }
  else
    st->b = st->window;

  if (st->ba) XFillRectangle(st->dpy, st->ba, st->gcClear, 0, 0, st->scrWidth, st->scrHeight);
  if (st->bb) XFillRectangle(st->dpy, st->bb, st->gcClear, 0, 0, st->scrWidth, st->scrHeight);

  simulation_init(st);

  return st;
}

/*static void draw_searcher(struct state *st, Drawable curr_window, int i)*/
/*{*/
  /*Point r1, r2;*/
  /*PList *l;*/

  /*if(st->searcher[i] == NULL)*/
    /*return;*/

  /*XSetForeground(st->dpy, st->gcDraw, st->searcher[i]->color);*/

  /*r1.x = X(st->searcher[i]->r.x) + st->searcher[i]->rs;*/
  /*r1.y = Y(st->searcher[i]->r.y);*/

  /*XFillRectangle(st->dpy, curr_window, st->gcDraw, r1.x - 2, r1.y - 2, 4, 4);*/

  /*for(l = st->searcher[i]->hist; l != NULL; l = l->next) {*/

    /*r2.x = X(l->r.x) + st->searcher[i]->rs;*/
    /*r2.y = Y(l->r.y);*/

    /*XDrawLine(st->dpy, curr_window, st->gcDraw, r1.x, r1.y, r2.x, r2.y);*/

    /*r1 = r2;*/
  /*}*/

/*}*/

/*static void draw_image(struct state *st, Drawable curr_window)*/
/*{*/
  /*int i, j;*/
  /*int x, y;*/

  /*for(i = 0; i < st->max_src; i++) {*/

    /*if(st->source[i] == NULL)*/
      /*continue;*/

    /*XSetForeground(st->dpy, st->gcDraw, st->source[i]->color);*/

    /*if(st->source[i]->inv_rate > 0) {*/

      /*if(st->max_searcher > 0) {*/
        /*x = (int) X(st->source[i]->r.x);*/
        /*y = (int) Y(st->source[i]->r.y);*/
        /*j = st->dx * (MAX_INV_RATE + 1 - st->source[i]->inv_rate) / (2 * MAX_INV_RATE);*/
        /*if(j == 0)*/
          /*j = 1;*/
        /*XFillArc(st->dpy, curr_window, st->gcDraw, x - j, y - j, 2 * j, 2 * j, 0, 360 * 64);*/
      /*}}*/

    /*for(j = 0; j < st->source[i]->n; j++) {*/

      /*if(st->source[i]->yv[j].v == 2)*/
        /*continue;*/

       /*Move the particles slightly off lattice */
      /*x =  X(st->source[i]->r.x + 1 + j) + RND(st->dx);*/
      /*y = Y(st->source[i]->r.y + st->source[i]->yv[j].y) + RND(st->dy);*/
      /*XFillArc(st->dpy, curr_window, st->gcDraw, x - 2, y - 2, 4, 4, 0, 360 * 64);*/
    /*}*/

  /*}*/

  /*for(i = 0; i < st->max_searcher; i++)*/
    /*draw_searcher(st, curr_window, i);*/

/*}*/

static void animate_dynamicrrt(struct state *st, Drawable curr_window)
{
  int i, j;
  Bool dead;

  for(i = 0; i < st->max_src; i++) {

    if(st->source[i] == NULL)
      continue;

    evolve_source(st->source[i]);

    /* reap dead sources for which all particles are gone */
    if(st->source[i]->inv_rate == 0) {

      dead = True;

      for(j = 0; j < st->source[i]->n; j++) {
        if(st->source[i]->yv[j].v != 2) {
          dead = False;
          break;
        }
      }

      if(dead == True) {
        destroy_source(st->source[i]);
        st->source[i] = NULL;
      }
    }
  }

  /* Decide if we want to add new  sources */

  for(i = 0; i < st->max_src; i++) {
    if(st->source[i] == NULL && RND(st->max_dist * st->max_src) == 0)
      st->source[i] = new_source(st);
  }

  if(st->max_searcher == 0) { /* kill some sources when searchers don't do that */
    for(i = 0; i < st->max_src; i++) {
      if(st->source[i] != NULL && RND(st->max_dist * st->max_src) == 0) {
        destroy_source(st->source[i]);
        st->source[i] = 0;
      }
    }
  }

  /* Now deal with searchers */

  for(i = 0; i < st->max_searcher; i++) {

    if((st->searcher[i] != NULL) && (st->searcher[i]->state == DONE)) {
      destroy_searcher(st->searcher[i]);
      st->searcher[i] = NULL;
    }

    if(st->searcher[i] == NULL) {

      if(RND(st->max_dist * st->max_searcher) == 0) {

        st->searcher[i] = new_searcher(st);

      }
    }

    if(st->searcher[i] == NULL)
      continue;

    /* Check if searcher found a source or missed all of them */
    for(j = 0; j < st->max_src; j++) {

      if(st->source[j] == NULL || st->source[j]->inv_rate == 0)
        continue;

      if(st->searcher[i]->r.x < 0) {
        st->searcher[i]->state = DONE;
        break;
      }

      if((st->source[j]->r.y == st->searcher[i]->r.y) &&
          (st->source[j]->r.x == st->searcher[i]->r.x)) {
        st->searcher[i]->state = DONE;
        st->source[j]->inv_rate = 0;  /* source disappears */

        /* Make it flash */
        st->searcher[i]->color = WhitePixel(st->dpy, DefaultScreen(st->dpy));

        break;
      }
    }

    st->searcher[i]->c = 0; /* set it here in case we don't get to get_v() */

    /* Find the concentration at searcher's location */

    if(st->searcher[i]->state != DONE) {
      for(j = 0; j < st->max_src; j++) {

        if(st->source[j] == NULL)
          continue;

        get_v(st->source[j], st->searcher[i]);

        if(st->searcher[i]->c == 1)
          break;
      }
    }

    move_searcher(st->searcher[i]);

  }

  draw_image(st, curr_window);
}

static unsigned long dynamicrrt_draw(Display *dpy, Window window, void *closure)
{
  struct state *st = (struct state *) closure;
  XWindowAttributes wa;
  int w, h;

  XGetWindowAttributes(st->dpy, st->window, &wa);

  w = wa.width;
  h = wa.height;

  if(w != st->scrWidth || h != st->scrHeight) {
    st->scrWidth = w;
    st->scrHeight = h;
    st->ax = st->scrWidth / (double) st->max_dist;
    st->ay = st->scrHeight / (2. * st->max_dist);
    st->bx = 0.;
    st->by = 0.;

    if((st->dx = st->scrWidth / (2 * st->max_dist)) == 0)
      st->dx = 1;
    if((st->dy = st->scrHeight / (4 * st->max_dist)) == 0)
      st->dy = 1;
    XSetLineAttributes(st->dpy, st->gcDraw, st->dx / 3 + 1, LineSolid, CapRound, JoinRound);
  }

  XFillRectangle (st->dpy, st->b, st->gcClear, 0, 0, st->scrWidth, st->scrHeight);
  animate_dynamicrrt(st, st->b);

#ifdef HAVE_DOUBLE_BUFFER_EXTENSION
  if (st->backb) {
    XdbeSwapInfo info[1];
    info[0].swap_window = st->window;
    info[0].swap_action = XdbeUndefined;
    XdbeSwapBuffers(st->dpy, info, 1);
  }
  else
#endif
    if (st->dbuf) {
      XCopyArea(st->dpy, st->b, st->window, st->gcClear, 0, 0,
          st->scrWidth, st->scrHeight, 0, 0);
      st->b = (st->b == st->ba ? st->bb : st->ba);
    }

  return st->delay;
}



static void dynamicrrt_reshape(Display *dpy, Window window, void *closure,
    unsigned int w, unsigned int h)
{
}

static Bool dynamicrrt_event (Display *dpy, Window window, void *closure, XEvent *event)
{
  return False;
}

static void dynamicrrt_free(Display *dpy, Window window, void *closure)
{
  struct state *st = (struct state *) closure;
  int i;
  if (st->source) {
    for (i = 0; i < st->max_src; i++)
      if (st->source[i]) destroy_source (st->source[i]);
    free (st->source);
  }
  if (st->searcher) {
    for (i = 0; i < st->max_searcher; i++)
      if (st->searcher[i]) destroy_searcher (st->searcher[i]);
    free (st->searcher);
  }
  free (st);
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
  { "-delay"          , ".delay"       , XrmoptionSepArg, 0 } ,
  { "-obstacle_radius", ".radius"      , XrmoptionSepArg, 0 } ,
  { "-robot-radius"   , ".robot_radius", XrmoptionSepArg, 0 } ,
  { "-max-speed"      , ".max_speed"   , XrmoptionSepArg, 0 } ,
  { "-robot-speed"    , ".robot_speed" , XrmoptionSepArg, 0 } ,
  { "-sources"        , ".sources"     , XrmoptionSepArg, 0 } ,
  { "-obstacles"      , ".obstacles"   , XrmoptionSepArg, 0 } ,
  { 0                 , 0              , 0              , 0 }
};


XSCREENSAVER_MODULE ("DynamicRRT", dynamicrrt)
