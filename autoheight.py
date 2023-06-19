#!/usr/bin/env python3

# 3D-point height calculator for spreadsheets

from pynput import keyboard
import numpy as np
from tkinter import * # Standard Tkinter practice
from tkinter import ttk # Newer 'themed widgets'
from tkinter import filedialog
from tkinter import messagebox
import re
from pathlib import Path
import platform
import time
import sys
import traceback

if TkVersion < 8.6:
    print(f"The Tk GUI library on this system is {Tcl().eval('info patchlevel')}. Tk version >= 8.6 is required.", file=sys.stderr)
    sys.exit(1)

HEIGHT_HOTKEY = keyboard.HotKey.parse('<ctrl>+<alt>+p')
MISS_VALUE = 0.0
PRECISION = np.float32
PATH_OBJ_ICON = "images/obj_16.png"
PATH_OBJECT_ICON = "images/object_16.png"
PATH_GROUP_ICON = "images/group_16.png"
PATH_MANUAL = "manual.txt"
DARWIN = platform.system() == 'Darwin'
WINDOWS = platform.system() == 'Windows'
PATH_APP_ICON = "images/app_32.ico" if WINDOWS else '' if DARWIN else "images/app_32.xbm"
TTK_GEOMETRY_RE = re.compile(r'(?P<width>\d*)x(?P<height>\d*)(?P<x>(?:\+|-)\d*)(?P<y>(?:\+|-)\d*)', flags=re.ASCII)

APP_TITLE = 'AutoHeight'
DEFAULT_OBJECT_NAME = "default"
DEFAULT_GROUP_NAME = "default"
XYZ_COLUMN_OFFSETS = {3: 0} # CELLS_PER_ROW : X_COL_OFFSET_FROM_LEFT

NINTENDO_KMP_XYZ_COLUMN_OFFSETS = True
if NINTENDO_KMP_XYZ_COLUMN_OFFSETS:
    XYZ_COLUMN_OFFSETS[9] = 1 # StartPos, Checkpoint, Respawn, Cannon, MSPT
    XYZ_COLUMN_OFFSETS[7] = 1 # EnemyRoute, ItemRoute
    XYZ_COLUMN_OFFSETS[20] = 1 # Object
    XYZ_COLUMN_OFFSETS[6] = 1 # Route
    XYZ_COLUMN_OFFSETS[17] = 5 # AREA
    XYZ_COLUMN_OFFSETS[25] = 10 # Camera


class Obj():
    object_tag = 'o '
    group_tag = 'g '
    vertex_tag = 'v '
    face_tag = 'f '

    class Object():
        def __init__(self, name=None):
            self.name = name
            self.groups = [Obj.Group()] # Default group
            self.tri_count = 0
            self.up_tri_count = 0
            self.down_tri_count = 0

    class Group():
        def __init__(self, name=None):
            self.name = name
            self.up_tris = None
            self.down_tris = None
            self.tri_count = 0

    @staticmethod
    def mtx_orient_from_axes(forward='Y', up='Z'):
        '''Convert forward and up directions to a rotation matrix.
        Return identity matrix by default'''
        directions = {'X':(1,0,0), 'Y':(0,1,0), 'Z':(0,0,1), '-X':(-1,0,0), '-Y':(0,-1,0), '-Z':(0,0,-1)}
        if forward not in directions: raise ValueError
        if up not in directions: raise ValueError
        if forward[-1] == up[-1]: raise ValueError # Forward and up directions must be orthogonal
        return np.column_stack((np.cross(directions[forward], directions[up]), directions[forward], directions[up]))
    
    @staticmethod
    def normal_z(vertices, face):
        v1 = vertices[face[0]]
        v2 = vertices[face[1]]
        v3 = vertices[face[2]]
        return np.cross(v2 - v1, v3 - v1)[2]
    
    @staticmethod
    def max_z(ray, meshes):
        '''Calculate the point of intersection with the most positive
        z coordinate. Return that z coordinate or None if no intersection.'''
        ray_origin = np.array((ray[0], ray[1], 0))
        ray_direction = np.array((0, 0, 1))

        z_max = None
        for vertices, face_lists in meshes:
            for face_list in face_lists:
                for face in face_list:
                    v1 = vertices[face[0]]
                    v2 = vertices[face[1]]
                    v3 = vertices[face[2]]
                    mtx = np.column_stack((v2 - v1, v3 - v1, -ray_direction))
                    u, v, z = np.linalg.solve(mtx, ray_origin - v1)
                    if 0 <= u and 0 <= v and u + v <= 1 and (z_max is None or z > z_max): z_max = z
        return z_max
    
    def __init__(self, file, forward='-Z', up='Y'):

        self.tri_count = 0
        self.up_tri_count = 0
        self.down_tri_count = 0
        self.non_tri_count = 0

        file.seek(0)
        vertex_count = 0
        face_count = 0
        for line in file:
            if line.startswith(Obj.vertex_tag):
                vertex_count += 1
            elif line.startswith(Obj.face_tag):
                face_vert_count = len(line.split()) - 1
                if face_vert_count == 3:
                    face_count += 1
                else:
                    self.non_tri_count += 1

        self.vertices = np.zeros((vertex_count, 3), dtype=PRECISION)
        self.objects = [Obj.Object()] # Default object

        first_face = 0
        next_face = 0
        next_vertex = 0
        faces = np.zeros((face_count, 3), dtype=np.uint32)
        mtx_transform = np.transpose(Obj.mtx_orient_from_axes(forward=forward, up=up)) # A^-1 == A^t

        file.seek(0)
        for line in file:
            if line.startswith(Obj.vertex_tag):
                self.vertices[next_vertex] = mtx_transform @ np.array(line.split()[1:], dtype=PRECISION)
                next_vertex += 1

            elif line.startswith(Obj.face_tag):
                vertex_offsets = [int(vertex_attributes.split('/')[0]) for vertex_attributes in line.split()[1:]]
                if len(vertex_offsets) != 3: continue
                for i in range(3):
                    vertex_offset = vertex_offsets[i] - 1
                    if vertex_offset < 0: vertex_offset += vertex_count
                    faces[next_face][i] = vertex_offset
                next_face += 1
                
            elif line.startswith(Obj.group_tag):
                self.objects[-1].groups[-1].up_tris = faces[first_face:next_face, :] # Returns shallow view
                first_face = next_face
                self.objects[-1].groups.append(Obj.Group(line.split()[1]))

            elif line.startswith(Obj.object_tag):
                self.objects[-1].groups[-1].up_tris = faces[first_face:next_face, :]
                first_face = next_face
                self.objects.append(Obj.Object(line.split()[1]))

        self.objects[-1].groups[-1].up_tris = faces[first_face:next_face, :]

        for o in self.objects:
            for group in o.groups:
                normal_zs = np.array([Obj.normal_z(self.vertices, face) for face in group.up_tris])
                tri_count = len(group.up_tris)
                group.down_tris = group.up_tris[normal_zs < 0]
                down_tri_count = len(group.down_tris)
                group.up_tris = group.up_tris[normal_zs > 0]
                up_tri_count = len(group.up_tris)

                group.tri_count = tri_count
                o.tri_count += tri_count
                o.up_tri_count += up_tri_count
                o.down_tri_count += down_tri_count
                self.tri_count += tri_count
                self.up_tri_count += up_tri_count
                self.down_tri_count += down_tri_count

        # Remove empty groups and empty objects
        for o in self.objects: o.groups = [group for group in o.groups if group.up_tris.size or group.down_tris.size]
        self.objects = [o for o in self.objects if o.groups]

        self.box_min = (np.amin(self.vertices[:, 0]), np.amin(self.vertices[:, 1]), np.amin(self.vertices[:, 2]))
        self.box_max = (np.amax(self.vertices[:, 0]), np.amax(self.vertices[:, 1]), np.amax(self.vertices[:, 2]))


class TaggingTreeView(ttk.Treeview):
    def get_descendants(self, node, descendants):
        '''Append all descendent nodes of node to descendants'''
        for child in self.get_children(node):
            descendants.append(child)
            self.get_descendants(child, descendants)
    
    def add_tag(self, node, tag) -> bool:
        '''Return whether tag added'''
        tags = self.item(node, 'tags')
        if tag in tags: return False
        self.item(node, tags=(*tags, tag))
        return True

    def remove_tag(self, node, tag) -> bool:
        '''Return whether tag removed'''
        tags = self.item(node, 'tags')
        if tag not in tags: return False
        self.item(node, tags=[t for t in tags if t != tag])
        return True


class AutoHeight:
    pass_tag = '0'
    up_face_mode = 'Up Faces'
    down_face_mode = 'Down Faces'
    all_face_mode = 'All Faces'

    def __init__(self, root):

        self.hotkey = keyboard.HotKey(HEIGHT_HOTKEY, self.process_highlighted_cells)
        self.controller = keyboard.Controller()
        self.listener = None

        self.root = root
        root.title(APP_TITLE)
        root.iconbitmap(PATH_APP_ICON)
        root.columnconfigure(0, weight=1)
        root.rowconfigure(0, weight=1)
        def close_root():
            self.listener.stop()
            root.destroy()
        root.protocol("WM_DELETE_WINDOW", close_root)

        def show_error(_, *args):
            error = traceback.format_exception(*args)
            print(error, file=sys.stderr)
            messagebox.showerror('Exception', error)
        Tk.report_callback_exception = show_error

        main_window_frame = ttk.Frame(root)
        main_window_frame.grid(column=0, row=0, sticky=(N, E, S, W))
        main_window_frame.columnconfigure(0, weight=4)
        main_window_frame.columnconfigure(1, weight=0)
        main_window_frame.rowconfigure(0, weight=1)

        tree_frame = ttk.Frame(main_window_frame)
        tree_frame.grid(column=0, row=0, sticky=(N, E, S, W))
        tree_frame.columnconfigure(0, weight=1)
        tree_frame.rowconfigure(0, weight=1)

        self.tree = tree = TaggingTreeView(tree_frame, show="tree")
        tree.tag_configure(AutoHeight.pass_tag, background='#DFDFDF')
        tree.items = {}
        tree.columnconfigure(0, weight=1)
        tree.rowconfigure(0, weight=1)

        def photo_image(file):
            try:
                return PhotoImage(file=file)
            except TclError as e:
                print(e, file=sys.stderr)
                return ''
        tree.obj_icon = photo_image(PATH_OBJ_ICON)
        tree.object_icon = photo_image(PATH_OBJECT_ICON)
        tree.group_icon = photo_image(PATH_GROUP_ICON)

        tree_scrollbar = ttk.Scrollbar(tree, orient=VERTICAL, command=tree.yview)
        tree_scrollbar.grid(column=1, row=0, rowspan=2, sticky=(N, S))
        tree['yscrollcommand'] = tree_scrollbar.set
        tree.grid(column=0, row=0, sticky=(N, E, S, W))
        tree_scrollbar.grid_configure(padx=2, pady=2)

        tree_stats_frame = ttk.Frame(tree_frame, borderwidth=5)
        tree_stats_frame.columnconfigure(1, minsize=10)
        tree_stats_frame.grid(column=0, row=1, sticky=(N, E, S, W))

        self.tree_stat_titles = StringVar()
        self.tree_stat_titles.set("Select a mesh from the treeview")
        self.tree_stats = StringVar()
        self.tree_stats.set("")
        tree_stat_titles_label = ttk.Label(tree_stats_frame, textvariable=self.tree_stat_titles)
        tree_stat_titles_label.grid(column=0, row=0, sticky=E)
        tree_stats_label = ttk.Label(tree_stats_frame, textvariable=self.tree_stats)
        tree_stats_label.grid(column=2, row=0, sticky=W)
        tree.bind('<<TreeviewSelect>>', self.update_tree_stats)

        settings_frame = ttk.Frame(main_window_frame, borderwidth=10)
        settings_frame.grid(column=1, row=0, sticky=(N, E, S, W))
        settings_frame.columnconfigure(0, weight=1)
        settings_frame.columnconfigure(1, weight=1)

        load_obj_button = ttk.Button(settings_frame, text="Load OBJ", command=self.import_obj)
        load_obj_button.grid(column=0, row=0)

        remove_obj_button = ttk.Button(settings_frame, text="Remove OBJ", command=self.remove_selected_objs)
        remove_obj_button.grid(column=1, row=0)

        z_offset_frame = ttk.Frame(settings_frame)
        z_offset_frame.grid(column=0, row=1, columnspan=2, sticky=(N, E, S, W))
        z_offset_frame.columnconfigure(0, weight=1)
        z_offset_label = ttk.Label(z_offset_frame, text="Height Offset")
        z_offset_label.grid(column=0, row=0, sticky=W)
        self.z_offset = DoubleVar()
        self.z_offset.set(0)
        z_offset_entry = ttk.Entry(z_offset_frame, textvariable=self.z_offset)
        z_offset_entry.grid(column=0, row=1, sticky=(E, W))

        collision_labelframe = ttk.Labelframe(settings_frame, text="Mesh Collision")
        collision_labelframe.grid(column=0, row=2, columnspan=2, sticky=(N, E, S, W))
        collision_labelframe.columnconfigure(0, weight=1)
        collision_labelframe.columnconfigure(1, weight=1)

        selected_collision_off_button = ttk.Button(collision_labelframe, text="Hide", command=self.selected_collision_off)
        selected_collision_off_button.grid(column=0, row=0)

        selected_collision_on_button = ttk.Button(collision_labelframe, text="Unhide", command=self.selected_collision_on)
        selected_collision_on_button.grid(column=1, row=0)

        face_mode_frame = ttk.Frame(collision_labelframe)
        face_mode_frame.grid(column=0, row=2, columnspan=2, sticky=(N, E, S, W))
        face_mode_frame.columnconfigure(0, weight=1)
        
        self.face_mode = StringVar()
        self.face_mode.set(AutoHeight.up_face_mode)
        face_mode_label = ttk.Label(face_mode_frame, text="Face Collision")
        face_mode_label.grid(column=0, row=0, sticky=W)
        face_mode_combobox = ttk.Combobox(face_mode_frame, textvariable=self.face_mode)
        face_mode_combobox['values'] = (AutoHeight.up_face_mode, AutoHeight.down_face_mode, AutoHeight.all_face_mode)
        face_mode_combobox.state(["readonly"])
        face_mode_combobox.grid(column=0, row=1, sticky=(E, W))

        spreadsheet_labelframe = ttk.Labelframe(settings_frame, text="Spreadsheet Format")
        spreadsheet_labelframe.grid(column=0, row=3, columnspan=2, sticky=(N, E, S, W))
        spreadsheet_labelframe.columnconfigure(0, weight=1)
        spreadsheet_labelframe.columnconfigure(1, weight=1)

        def force_orth_axes(event):
            forward_axis = forward_combobox.get()
            up_axis = up_combobox.get()
            if forward_axis[-1] == up_axis[-1]:
                next_axis = {'X': 'Y', 'Y': 'Z', 'Z': 'X', '-X': '-Y', '-Y': '-Z', '-Z': '-X'}
                if event.widget is forward_combobox:
                    up_combobox.set(next_axis[up_axis])
                else:
                    forward_combobox.set(next_axis[forward_axis])
        
        scale_label = ttk.Label(spreadsheet_labelframe, text="Scale")
        scale_label.grid(column=0, row=0, sticky=(N, E))
        self.scale = StringVar()
        scale_entry = ttk.Entry(spreadsheet_labelframe, textvariable=self.scale)
        self.scale.set(1)
        scale_entry.grid(column=1, row=0, sticky=(E, W))

        forward_label = ttk.Label(spreadsheet_labelframe, text="Forward")
        forward_label.grid(column=0, row=1, sticky=E)
        self.forward = StringVar()
        forward_combobox = ttk.Combobox(spreadsheet_labelframe, textvariable=self.forward)
        forward_combobox['values'] = ('X', 'Y', 'Z', '-X', '-Y', '-Z')
        self.forward.set('-Z')
        forward_combobox.state(["readonly"])
        forward_combobox.grid(column=1, row=1, sticky=(E, W))
        forward_combobox.bind('<<ComboboxSelected>>', force_orth_axes)

        up_label = ttk.Label(spreadsheet_labelframe, text="Up")
        up_label.grid(column=0, row=2, sticky=E)
        self.up = StringVar()
        up_combobox = ttk.Combobox(spreadsheet_labelframe, textvariable=self.up)
        up_combobox['values'] = ('X', 'Y', 'Z', '-X', '-Y', '-Z')
        self.up.set('Y')
        up_combobox.state(["readonly"])
        up_combobox.grid(column=1, row=2, sticky=(E, W))
        up_combobox.bind('<<ComboboxSelected>>', force_orth_axes)

        button_hotkey = ttk.Button(settings_frame, text="Hotkey", command=self.manage_hotkey)
        if DARWIN: button_hotkey.state(['disabled']) # prevents macOS-specific "illegal hardware instruction" caused when starting pynput.keyboard.Listener within tkinter mainloop
        button_hotkey.grid(column=0, row=4)

        self.help_open = False
        button_help = ttk.Button(settings_frame, text="Help", command=self.help_dialog)
        button_help.grid(column=1, row=4)

        for child in settings_frame.winfo_children():
            child.grid_configure(padx=10, pady=10)
        
        for child in collision_labelframe.winfo_children():
            child.grid_configure(padx=5, pady=5)
        
        for child in spreadsheet_labelframe.winfo_children():
            child.grid_configure(padx=5, pady=5)

        self.start_hotkey()

    def update_tree_stats(self, event):
        tree = self.tree
        tree_items = tree.items
        tree_stat_titles = self.tree_stat_titles
        tree_stats = self.tree_stats

        node = tree.focus()
        if not node:
            tree_stat_titles.set("Select a mesh from the treeview")
            tree_stats.set("")
            return
        item = tree_items[node]
        if type(item) is Obj:
            tree_stat_titles.set("OBJ\nVertices\nFaces\nTriangles\nBoxMin\nBoxMax")
            tree_stats.set(f'\n{len(item.vertices)}\n{item.tri_count + item.non_tri_count}\n{item.tri_count}\n{item.box_min}\n{item.box_max}')
        elif type(item) is Obj.Object:
            tree_stat_titles.set("OBJ Object\nUp Tris\nDown Tris\nOrth Tris")
            tree_stats.set(f'\n{item.up_tri_count}\n{item.down_tri_count}\n{item.tri_count - item.up_tri_count - item.down_tri_count}')
        elif type(item) is Obj.Group:
            tree_stat_titles.set("OBJ Object\nUp Tris\nDown Tris\nOrth Tris")
            tree_stats.set(f'\n{len(item.up_tris)}\n{len(item.down_tris)}\n{item.tri_count - len(item.up_tris) - len(item.down_tris)}')

    def selected_collision_on(self):
        tree = self.tree
        pass_tag = AutoHeight.pass_tag
        root = self.root
        selection = tree.selection()

        if not selection:
            self.all_collision_on()
            return

        for node in selection:
            if not tree.remove_tag(node, pass_tag): return

            # Remove pass tag from all descendents
            descendants = []
            tree.get_descendants(node, descendants)
            for descendant in descendants: tree.remove_tag(descendant, pass_tag)
            
            # Remove pass tag from parent until parent without pass tag
            parent = tree.parent(node)
            while parent:
                if not tree.remove_tag(parent, pass_tag): break
                parent = tree.parent(parent)

    def selected_collision_off(self):
        tree = self.tree
        pass_tag = AutoHeight.pass_tag
        root = self.root
        selection = tree.selection()

        if not selection:
            self.all_collision_off()
            return

        for node in selection:
            if not tree.add_tag(node, pass_tag): continue

            # Add pass tag to all descendents
            descendants = []
            tree.get_descendants(node, descendants)
            for descendant in descendants:
                tree.add_tag(descendant, pass_tag)
            
            # Give pass tag to parent until at least one child doesn't have pass tag
            parent = tree.parent(node)
            while parent:
                siblings = tree.get_children(parent)
                if not all(pass_tag in tree.item(sibling, 'tags') for sibling in siblings): break
                tree.add_tag(parent, pass_tag)
                parent = tree.parent(parent)

    def all_collision_on(self):
        tree = self.tree
        pass_tag = AutoHeight.pass_tag
        nodes = []
        tree.get_descendants('', nodes)
        for node in nodes: tree.remove_tag(node, pass_tag)

    def all_collision_off(self):
        tree = self.tree
        pass_tag = AutoHeight.pass_tag
        nodes = []
        tree.get_descendants('', nodes)
        for node in nodes: tree.add_tag(node, pass_tag)

    def remove_selected_objs(self):
        tree = self.tree
        tree_items = tree.items
        root = self.root
        obj_nodes = [node for node in tree.selection() if not tree.parent(node)]
        if not obj_nodes:
            messagebox.showwarning(
                message="Select OBJ from the treeview",
                title="Empty selection",
                parent=root, icon='warning')
            return
        for obj_node in obj_nodes:
            nodes = []
            tree.get_descendants(obj_node, nodes)
            for node in nodes: del tree_items[node]
            del tree_items[obj_node]
            tree.delete(obj_node)

    def manage_hotkey(self):
        if self.listener and self.listener.running:
            if messagebox.askyesno(
                message="Hotkey is running. Stop hotkey?",
                title="Manage Hotkey",
                parent=self.root, icon='warning'): self.listener.stop()
        else:
            if messagebox.askyesno(
                message="Hotkey is off. Start Hotkey?",
                title="Manage Hotkey",
                parent=self.root, icon='warning'): self.start_hotkey()

    def start_hotkey(self):
        self.listener = keyboard.Listener(
            on_press=lambda key: self.hotkey.press(self.listener.canonical(key)),
            on_release=lambda key: self.hotkey.release(self.listener.canonical(key)))
        self.listener.start()
    
    @staticmethod
    def log(message):
        print(f'{APP_TITLE} {time.strftime("%H:%M")} - {message}')

    def process_highlighted_cells(self):
        controller = self.controller
        root = self.root
        tree = self.tree
        tree_items = tree.items
        pass_tag = AutoHeight.pass_tag
        face_mode = self.face_mode.get()
        z_offset = self.z_offset.get()
        scale = self.scale.get()
        forward = self.forward.get()
        up = self.up.get()

        for key in HEIGHT_HOTKEY: controller.release(key) # Sometimes pynput thinks hotkey is still pressed

        # Copy user selection, wait for OS, then fetch clipboard data
        with controller.pressed(keyboard.Key.ctrl):
            controller.tap('c')
        time.sleep(0.1)
        rows = [row.split() for row in root.clipboard_get().splitlines()]

        # Verify format of clipboard data
        cells_per_row = 0
        for row in rows:
            if row:
                if not cells_per_row:
                    cells_per_row = len(row)
                elif len(row) != cells_per_row:
                    AutoHeight.log('Format error: rows differ in number of cells')
                    return
        xyz_offset = XYZ_COLUMN_OFFSETS.get(cells_per_row)
        if xyz_offset is None:
            AutoHeight.log(f'Format error: row has {cells_per_row} cells, expected {list(XYZ_COLUMN_OFFSETS)}')
            return
        try:
            xyz_points = [np.array(row[xyz_offset: xyz_offset+3], dtype=PRECISION) if row else None for row in rows]
        except ValueError as e:
            AutoHeight.log(f'Format error: {e}')
            return
        
        # Move cursor to 'up' column
        axis_offsets = {'X':0, 'Y':1, 'Z':2}
        lefts = cells_per_row - (1 + xyz_offset + axis_offsets[up[-1]])
        for _ in range(lefts): controller.tap(keyboard.Key.left)
        
        # Move cursor to top row
        for _ in range(len(rows) - 1): controller.tap(keyboard.Key.up)
        
        # Create transform matrix
        try:
            scale = float(scale)
            if scale <= 0: raise ValueError
        except ValueError as e:
            self.scale.set(1)
            scale = 1
        mtx_spreadsheet_to_obj = np.transpose(Obj.mtx_orient_from_axes(forward=forward, up=up)) / scale
        
        # Gather enabled meshes
        meshes = []
        up_enabled = face_mode in (AutoHeight.up_face_mode, AutoHeight.all_face_mode)
        down_enabled = face_mode in (AutoHeight.down_face_mode, AutoHeight.all_face_mode)
        for obj_id in tree.get_children(''):
            if pass_tag in tree.item(obj_id, 'tags'): continue
            face_lists = []
            for o_id in tree.get_children(obj_id):
                if pass_tag in tree.item(o_id, 'tags'): continue
                for group_id in tree.get_children(o_id):
                    if pass_tag in tree.item(group_id, 'tags'): continue
                    group = tree_items[group_id]
                    if up_enabled and group.up_tris.size: face_lists.append(group.up_tris)
                    if down_enabled and group.down_tris.size: face_lists.append(group.down_tris)
            meshes.append((tree_items[obj_id].vertices, face_lists))

        # Write new Y values
        z_scale_obj_to_spreadsheet = -scale if up[0] == '-' else scale
        for xyz_point in xyz_points:
            if xyz_point is not None:
                max_z_result = Obj.max_z(mtx_spreadsheet_to_obj @ xyz_point, meshes)
                if max_z_result is None:
                    controller.type(str(MISS_VALUE))
                else:
                    controller.type(str(max_z_result * z_scale_obj_to_spreadsheet + z_offset))
            controller.tap(keyboard.Key.down)

    def import_obj(self):
        root = self.root
        tree = self.tree
        tree_items = tree.items
        
        filepath = filedialog.askopenfilename(title="Open", filetypes=(('Wavefront OBJ', '*.obj'), ("All files", "*.*")))
        if not filepath: return
        filename = Path(filepath).name

        obj_transform = self.transform_dialog()
        if not obj_transform: return
        
        with open(filepath, 'r') as file:
            obj = Obj(file, **obj_transform)

        if obj.non_tri_count:
            if not messagebox.askokcancel(
                message="This OBJ contains untriangulated faces. Untriangulated faces will be ignored.",
                title="Found untriangulated faces",
                parent=root, icon='warning'): return

        obj_id = tree.insert('', 'end', text=filename, image=tree.obj_icon)
        tree_items[obj_id] = obj
        for o in obj.objects:
            o_id = tree.insert(obj_id, 'end', text=o.name if o.name else DEFAULT_OBJECT_NAME, image=tree.object_icon)
            tree_items[o_id] = o
            for group in o.groups:
                group_id = tree.insert(o_id, 'end', text=group.name if group.name else DEFAULT_GROUP_NAME, image=tree.group_icon)
                tree_items[group_id] = group

    def help_dialog(self):

        if self.help_open: return
        self.help_open = True

        def dialog_close():
            self.help_open = False
            dialog.destroy()

        root = self.root
        root.iconbitmap(PATH_APP_ICON)

        dialog = Toplevel(root)
        dialog.title("Help")
        dialog.grid_columnconfigure(0, weight=1)
        dialog.grid_rowconfigure(0, weight=1)

        try:
            with open(PATH_MANUAL) as file:
                help_text = file.read()
        except FileNotFoundError:
            help_text = "Manual not found. See repo on GitHub instead."

        text = Text(dialog, width=100, height=10)
        text.insert('1.0', help_text)
        text['state'] = 'disabled'
        text.grid(column=0, row=0, sticky=(N, E, S, W))

        text_scrollbar = ttk.Scrollbar(dialog, orient=VERTICAL, command=text.yview)
        text['yscrollcommand'] = text_scrollbar.set
        text_scrollbar.grid(column=1, row=0, sticky=(N, S))
        text_scrollbar.grid_configure(padx=2, pady=2)
        
        centre_window(root, dialog, default_width=825, default_height=164)
        dialog.protocol("WM_DELETE_WINDOW", dialog_close)
        dialog.transient(root)
        dialog.wait_visibility()
        dialog.wait_window()

    def transform_dialog(self) -> dict:
        '''Ask for OBJ orientation from user'''

        def dialog_close():
            dialog.grab_release()
            dialog.destroy()
        
        def dialog_submit():
            transform['forward'] = forward_combobox.get()
            transform['up'] = up_combobox.get()
            dialog_close()
        
        def force_orth_axes(event):
            print(dialog.geometry())
            forward_axis = forward_combobox.get()
            up_axis = up_combobox.get()
            if forward_axis[-1] == up_axis[-1]:
                next_axis = {'X': 'Y', 'Y': 'Z', 'Z': 'X', '-X': '-Y', '-Y': '-Z', '-Z': '-X'}
                if event.widget is forward_combobox:
                    up_combobox.set(next_axis[up_axis])
                else:
                    forward_combobox.set(next_axis[forward_axis])
        
        transform = {}
        root = self.root
        dialog = Toplevel(root)
        dialog.title("About this OBJ")
        dialog.columnconfigure(0, weight=1)
        dialog.columnconfigure(1, weight=1)

        forward_label = ttk.Label(dialog, text="Forward")
        forward_label.grid(column=0, row=0, sticky=E)

        forward_combobox = ttk.Combobox(dialog, width=25)
        forward_combobox['values'] = ('X', 'Y', 'Z', '-X', '-Y', '-Z')
        forward_combobox.set('-Z')
        forward_combobox.state(["readonly"])
        forward_combobox.grid(column=1, row=0, sticky=(E, W))
        forward_combobox.bind('<<ComboboxSelected>>', force_orth_axes)

        up_label = ttk.Label(dialog, text="Up")
        up_label.grid(column=0, row=1, sticky=E)

        up_combobox = ttk.Combobox(dialog, width=25)
        up_combobox['values'] = ('X', 'Y', 'Z', '-X', '-Y', '-Z')
        up_combobox.set('Y')
        up_combobox.state(["readonly"])
        up_combobox.grid(column=1, row=1, sticky=(E, W))
        up_combobox.bind('<<ComboboxSelected>>', force_orth_axes)

        button_frame = ttk.Frame(dialog)
        button_frame.grid(column=0, row=2, columnspan=2, sticky=(N, E, S, W))
        button_frame.columnconfigure(0, weight=1)
        button_frame.columnconfigure(1, weight=1)
        ttk.Button(button_frame, text="OK", command=dialog_submit).grid(column=0, row=0)
        ttk.Button(button_frame, text="Cancel", command=dialog_close).grid(column=1, row=0)

        for child in dialog.winfo_children():
            child.grid_configure(padx=5, pady=5)

        centre_window(root, dialog, default_width=240, default_height=97)
        dialog.bind('<Return>', lambda _: dialog_submit())
        dialog.bind('<Escape>', lambda _: dialog_close())
        
        dialog.resizable(FALSE,FALSE)
        dialog.protocol("WM_DELETE_WINDOW", dialog_close)
        dialog.transient(root)
        root.iconbitmap(PATH_APP_ICON)
        dialog.wait_visibility()
        dialog.grab_set()
        dialog.wait_window()

        return transform


def centre_window(reference, target, default_width=1, default_height=1):
    '''Centre target window relative to reference window.
    Width and height of window not yet gridded is 1'''
    ref_m = TTK_GEOMETRY_RE.match(reference.geometry())
    tar_m = TTK_GEOMETRY_RE.match(target.geometry())
    if not ref_m or not tar_m: return

    ref_width = int(ref_m.group('width'))
    ref_height = int(ref_m.group('height'))
    ref_x = int(ref_m.group('x'))
    ref_y = int(ref_m.group('y'))
    tar_width = int(tar_m.group('width'))
    tar_height = int(tar_m.group('height'))
    if tar_width == 1 and tar_height == 1:
        tar_width = default_width
        tar_height = default_height
    centre_x = ref_x + (ref_width - tar_width) // 2
    centre_y = ref_y + (ref_height - tar_height) // 2
    target.geometry(f'{centre_x:+}{centre_y:+}')


def main():
    root = Tk()
    autoheight = AutoHeight(root)
    root.mainloop()


if __name__ == '__main__':
    main()