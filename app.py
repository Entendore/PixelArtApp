# ==========================================
# 1. IMPORTS & GLOBALS
# ==========================================
import os
import time
import random
import json
import glob
import math
import logging
import zipfile
import io
import colorsys
import tempfile
import threading
from array import array
from kivy.app import App
from kivy.uix.widget import Widget
from kivy.uix.boxlayout import BoxLayout
from kivy.uix.button import Button
from kivy.uix.togglebutton import ToggleButton
from kivy.uix.spinner import Spinner
from kivy.uix.slider import Slider
from kivy.uix.label import Label
from kivy.uix.scrollview import ScrollView
from kivy.uix.gridlayout import GridLayout
from kivy.uix.textinput import TextInput
from kivy.uix.colorpicker import ColorWheel
from kivy.uix.popup import Popup
from kivy.uix.filechooser import FileChooserListView
from kivy.uix.progressbar import ProgressBar
from kivy.graphics import Color, Rectangle, Line, Fbo, ClearColor, ClearBuffers, RenderContext
from kivy.graphics.texture import Texture
from kivy.properties import ObjectProperty, ListProperty, NumericProperty, BooleanProperty, StringProperty
from kivy.lang import Builder
from kivy.core.window import Window
from kivy.graphics.transformation import Matrix
from kivy.clock import Clock
from kivy.event import EventDispatcher

try:
    from PIL import Image as PILImage
    PIL_AVAILABLE = True
except ImportError:
    PIL_AVAILABLE = False

try:
    import numpy as np
    NP_AVAILABLE = True
except ImportError:
    NP_AVAILABLE = False

logging.basicConfig(level=logging.DEBUG, format='%(asctime)s - [%(levelname)s] - %(name)s - %(message)s', handlers=[logging.FileHandler('pixel_editor.log', mode='w'), logging.StreamHandler()])
logger = logging.getLogger(__name__)

Window.size = (1300, 850)

# ==========================================
# 2. EVENT BUS (Observer Pattern)
# ==========================================
class EventBus(EventDispatcher):
    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.register_event_type('on_color_change')
        self.register_event_type('on_tool_change')

    def broadcast_color(self, color):
        self.dispatch('on_color_change', color)

    def broadcast_tool(self, tool_name):
        self.dispatch('on_tool_change', tool_name)

event_bus = EventBus()

# ==========================================
# 3. UTILITY FUNCTIONS
# ==========================================
def show_error_popup(title, message):
    content = BoxLayout(orientation='vertical', padding=10, spacing=10)
    content.add_widget(Label(text=message, color=(1,1,1,1)))
    btn = Button(text='Close', size_hint=(1, 0.2))
    content.add_widget(btn)
    popup = Popup(title=title, content=content, size_hint=(0.6, 0.4))
    btn.bind(on_press=popup.dismiss)
    popup.open()

def hex_to_rgb(h):
    h = h.lstrip('#')
    return tuple(int(h[i:i+2], 16)/255.0 for i in (0, 2, 4)) + (1.0,)

# ==========================================
# 4. DATA MODELS (MVC Pattern)
# ==========================================
PALETTES = {
    'Recent': [],
    'Sweetie 16': [hex_to_rgb(h) for h in ['1a1c2c','5d275d','b13e53','ef7d57','ffcd75','a7f070','38b764','257179','29366f','3b5dc9','41a6f6','73eff7','f4f4f4','94b0c2','566c86','333c57']],
    'PICO-8': [hex_to_rgb(h) for h in ['000000','1D2B53','7E2553','008751','AB5236','5F574F','C2C3C7','FFF1E8','FF004D','FFA300','FFEC27','00E436','29ADFF','83769C','FF77A8','FFCCAA']]
}

class Layer:
    def __init__(self, name, grid_size, is_folder=False):
        self.name = name
        self.is_folder = is_folder
        self.visible = True
        self.alpha_locked = False
        self.blend_mode = "Normal"
        self.opacity = 1.0
        self.children = []
        self.pixels = None if is_folder else [[(0, 0, 0, 0) for _ in range(grid_size)] for _ in range(grid_size)]
        self.is_dirty = True
        self.texture = Texture.create(size=(grid_size, grid_size), colorfmt='rgba')
        self.texture.mag_filter = 'nearest'

class Frame:
    def __init__(self, grid_size):
        self.layers = [Layer("Background", grid_size)]
        self.history = []
        self.history_index = -1

class ProjectDocument:
    def __init__(self, grid_size=32):
        self.grid_size = grid_size
        self.is_composite_dirty = True
        self.reset_project()

    def reset_project(self):
        self.frames = [Frame(self.grid_size)]
        self.active_frame_index = 0
        self.active_layer = self.frames[0].layers[0]
        self.composite_pixels = self.create_empty_pixels()
        self.save_history()

    def create_empty_pixels(self):
        return [[(0, 0, 0, 0) for _ in range(self.grid_size)] for _ in range(self.grid_size)]

    def _layer_to_dict(self, layer):
        d = {
            "name": layer.name, "is_folder": layer.is_folder, "visible": layer.visible,
            "alpha_locked": layer.alpha_locked, "blend_mode": layer.blend_mode, "opacity": layer.opacity
        }
        if layer.is_folder: d["children"] = [self._layer_to_dict(c) for c in layer.children]
        else: d["pixels"] = [[list(px) for px in row] for row in layer.pixels]
        return d

    def _dict_to_layer(self, d, grid_size):
        layer = Layer(d.get("name", "Unnamed"), grid_size, d.get("is_folder", False))
        layer.visible = d.get("visible", True)
        layer.alpha_locked = d.get("alpha_locked", False)
        layer.blend_mode = d.get("blend_mode", "Normal")
        layer.opacity = d.get("opacity", 1.0)
        if layer.is_folder:
            for child_d in d.get("children", []): layer.children.append(self._dict_to_layer(child_d, grid_size))
        else:
            loaded_pixels = d.get("pixels", [])
            if len(loaded_pixels) == grid_size and all(len(r) == grid_size for r in loaded_pixels):
                layer.pixels = [[tuple(px) for px in row] for row in loaded_pixels]
            else: layer.pixels = [[(0, 0, 0, 0) for _ in range(grid_size)] for _ in range(grid_size)]
        return layer

    def save_history(self):
        frame = self.frames[self.active_frame_index]
        if frame.history_index < len(frame.history) - 1:
            frame.history = frame.history[:frame.history_index + 1]
        
        snap = {
            'active_name': self.active_layer.name,
            'layers': [self._layer_to_dict(l) for l in frame.layers]
        }
        frame.history.append(snap)
        frame.history_index += 1
        if len(frame.history) > 50:
            frame.history.pop(0)
            frame.history_index -= 1

    def undo(self):
        frame = self.frames[self.active_frame_index]
        if frame.history_index > 0:
            frame.history_index -= 1
            snap = frame.history[frame.history_index]
            frame.layers = [self._dict_to_layer(l, self.grid_size) for l in snap['layers']]
            self._restore_active_layer(frame, snap.get('active_name'))
            self.is_composite_dirty = True

    def redo(self):
        frame = self.frames[self.active_frame_index]
        if frame.history_index < len(frame.history) - 1:
            frame.history_index += 1
            snap = frame.history[frame.history_index]
            frame.layers = [self._dict_to_layer(l, self.grid_size) for l in snap['layers']]
            self._restore_active_layer(frame, snap.get('active_name'))
            self.is_composite_dirty = True

    def _restore_active_layer(self, frame, name):
        def search(layers):
            for l in layers:
                if l.name == name: return l
                if l.is_folder:
                    res = search(l.children)
                    if res: return res
            return None
        layer = search(frame.layers)
        self.active_layer = layer if layer else frame.layers[0]

# ==========================================
# 5. FILE I/O & ASSET MANAGEMENT
# ==========================================
def ensure_palette_directory():
    if not os.path.exists('palettes'): os.makedirs('palettes')
    filepath = 'palettes/custom_palettes.json'
    if not os.path.exists(filepath):
        with open(filepath, 'w') as f: json.dump({"palettes": {}}, f)

def load_custom_palettes():
    ensure_palette_directory()
    filepath = 'palettes/custom_palettes.json'
    try:
        with open(filepath, 'r') as f:
            data = json.load(f)
            for name, colors in data.get("palettes", {}).items():
                PALETTES[name] = [tuple(c) for c in colors]
    except Exception as e: logger.error(f"Error loading custom palettes: {e}")

def ensure_brush_directory():
    if not os.path.exists('brushes'): os.makedirs('brushes')
    filepath = 'brushes/custom_brushes.json'
    if not os.path.exists(filepath):
        with open(filepath, 'w') as f: json.dump({"brushes": [{"name": "Custom Soft Eraser", "shape": "soft_circle", "hardness": 0.2, "jitter": 0.0, "spacing": 0.1, "size_jitter": 0.0, "blend": True, "opacity_mult": 0.5}]}, f, indent=4)

def load_brush_packs():
    brushes = [
        {"name": "Pixel Pen", "shape": "square", "hardness": 1.0, "jitter": 0.0, "spacing": 0.1, "size_jitter": 0.0, "blend": False, "opacity_mult": 1.0},
        {"name": "Pencil", "shape": "square", "hardness": 1.0, "jitter": 0.0, "spacing": 0.1, "size_jitter": 0.0, "blend": True, "opacity_mult": 0.8},
        {"name": "Ink Pen", "shape": "circle", "hardness": 1.0, "jitter": 0.0, "spacing": 0.1, "size_jitter": 0.0, "blend": False, "opacity_mult": 1.0},
        {"name": "Soft Brush", "shape": "soft_circle", "hardness": 0.3, "jitter": 0.0, "spacing": 0.05, "size_jitter": 0.0, "blend": True, "opacity_mult": 0.5},
        {"name": "Marker", "shape": "square", "hardness": 1.0, "jitter": 0.0, "spacing": 0.1, "size_jitter": 0.0, "blend": True, "opacity_mult": 0.6},
        {"name": "Watercolor", "shape": "soft_circle", "hardness": 0.1, "jitter": 0.0, "spacing": 0.05, "size_jitter": 0.2, "blend": True, "opacity_mult": 0.15},
        {"name": "Spray", "shape": "scatter", "hardness": 1.0, "jitter": 0.7, "spacing": 0.2, "size_jitter": 0.5, "blend": False, "opacity_mult": 1.0},
        {"name": "Noise", "shape": "noise", "hardness": 1.0, "jitter": 0.5, "spacing": 0.1, "size_jitter": 0.2, "blend": False, "opacity_mult": 0.8},
        {"name": "Hatch", "shape": "hatch", "hardness": 1.0, "jitter": 0.0, "spacing": 0.1, "size_jitter": 0.0, "blend": True, "opacity_mult": 0.5},
        {"name": "Cross Hatch", "shape": "hatch_cross", "hardness": 1.0, "jitter": 0.0, "spacing": 0.1, "size_jitter": 0.0, "blend": True, "opacity_mult": 0.5},
        {"name": "Dither", "shape": "dither", "hardness": 1.0, "jitter": 0.0, "spacing": 0.1, "size_jitter": 0.0, "blend": True, "opacity_mult": 0.5},
        {"name": "Smudge/Blur", "shape": "blur", "hardness": 1.0, "jitter": 0.0, "spacing": 0.1, "size_jitter": 0.0, "blend": True, "opacity_mult": 1.0}
    ]
    ensure_brush_directory()
    for filepath in glob.glob('brushes/*.json'):
        try:
            with open(filepath, 'r') as f:
                data = json.load(f)
                brushes.extend(data.get('brushes', []))
        except Exception as e: logger.error(f"Error loading brush pack {filepath}: {e}")
    return brushes

load_custom_palettes()

# ==========================================
# 6. DIALOG FACTORY
# ==========================================
class DialogFactory:
    @staticmethod
    def create_popup(title, content, size_hint=(0.8, 0.8)):
        return Popup(title=title, content=content, size_hint=size_hint)

    @staticmethod
    def build_canvas_size_dialog(current_size, on_apply_callback):
        layout = BoxLayout(orientation='vertical', padding=10, spacing=10)
        controls = BoxLayout(orientation='horizontal', size_hint_y=0.4, spacing=5)
        controls.add_widget(Label(text='Size:', color=(1,1,1,1), size_hint_x=0.6))
        size_input = TextInput(text=str(current_size), multiline=False, input_filter='int')
        controls.add_widget(size_input)
        layout.add_widget(controls)
        
        chk_box = BoxLayout(orientation='horizontal', size_hint_y=0.2, spacing=5)
        keep_art_chk = ToggleButton(text='Keep Art', state='down')
        chk_box.add_widget(keep_art_chk)
        layout.add_widget(chk_box)
        
        btn_box = BoxLayout(orientation='horizontal', size_hint_y=0.4, spacing=5)
        apply_btn = Button(text='Apply', background_color=(0.2, 0.8, 0.2, 1))
        cancel_btn = Button(text='Cancel', background_color=(0.8, 0.2, 0.2, 1))
        btn_box.add_widget(apply_btn)
        btn_box.add_widget(cancel_btn)
        layout.add_widget(btn_box)

        popup = DialogFactory.create_popup('Canvas Size', layout, (0.5, 0.4))
        def do_apply(instance):
            try:
                new_size = int(size_input.text)
                if new_size > 0: on_apply_callback(new_size, keep_art_chk.state == 'down')
            except ValueError: pass
            popup.dismiss()
        apply_btn.bind(on_press=do_apply)
        cancel_btn.bind(on_press=popup.dismiss)
        return popup

# ==========================================
# 7. SHADERS & KV LAYOUT
# ==========================================
KV_CHECKERBOARD_FS = """
 $HEADER$ void main(void) {
    vec2 grid = floor(tex_coord0 * 8.0);
    float c = mod(grid.x + grid.y, 2.0);
    float col = mix(0.8, 1.0, c);
    gl_FragColor = vec4(col, col, col, 1.0);
}
"""

KV_LAYOUT = """
<LayerRow>:
    size_hint_y: None
    height: 45
    spacing: 2
    Widget: 
        size_hint_x: None
        width: root.indentation * 15
    ToggleButton: 
        text: 'V'
        state: 'down' if root.layer.visible else 'normal'
        size_hint_x: None
        width: 30
        background_color: (0.6, 0.2, 0.2, 1) if root.layer.visible else (0.2, 0.2, 0.2, 1)
        on_press: 
            root.layer.visible = not root.layer.visible
            app.root.canvas_widget.recalculate_composite()
            app.root.canvas_widget.redraw_pixels()
    TextInput: 
        text: root.layer.name
        multiline: False
        size_hint_x: 0.35
        foreground_color: 1, 1, 1, 1
        background_color: (0.3, 0.3, 0.5, 1) if root.layer == app.root.canvas_widget.project.active_layer else (0.15, 0.15, 0.18, 1)
        on_text: root.layer.name = self.text
        on_touch_down:
            app.root.canvas_widget.project.active_layer = root.layer
            app.root.update_layer_ui()
            super().on_touch_down(args[1])
    Spinner: 
        text: root.layer.blend_mode
        values: ['Normal', 'Multiply', 'Add', 'Overlay']
        size_hint_x: 0.35
        on_text:
            root.layer.blend_mode = self.text
            app.root.canvas_widget.recalculate_composite()
            app.root.canvas_widget.redraw_pixels()

<RootWidget>:
    orientation: 'vertical'
    canvas.before:
        Color:
            rgba: 0.12, 0.12, 0.15, 1
        Rectangle:
            pos: self.pos
            size: self.size

    BoxLayout:
        orientation: 'horizontal'
        size_hint_y: 0.92

        FloatLayout:
            size_hint: 0.53, 1
            PixelCanvas:
                id: canvas_widget
                size_hint: None, None
                size: 512, 512
                pos_hint: {'center_x': 0.5, 'center_y': 0.5}

        BoxLayout:
            orientation: 'vertical'
            size_hint: 0.25, 1
            padding: 10
            spacing: 8
            
            ColorWheel:
                id: color_wheel
                size_hint: 1, 0.25
                color: 1, 0, 0, 1
                
            BoxLayout:
                orientation: 'horizontal'
                size_hint: 1, 0.04
                spacing: 5
                Label:
                    text: 'Hex:'
                    color: 1, 1, 1, 1
                    size_hint_x: 0.2
                TextInput:
                    id: hex_input
                    text: 'FF0000'
                    multiline: False
                    size_hint_x: 0.4
                    on_text_validate: root.apply_hex_color(self.text)
                Button:
                    text: 'Apply'
                    size_hint_x: 0.2
                    on_press: root.apply_hex_color(hex_input.text)
                Button:
                    text: 'RGB'
                    size_hint_x: 0.1
                    on_press: root.open_color_slider_dialog('rgb')
                Button:
                    text: 'HSV'
                    size_hint_x: 0.1
                    on_press: root.open_color_slider_dialog('hsv')
            
            BoxLayout:
                orientation: 'horizontal'
                size_hint: 1, 0.06
                spacing: 5
                Spinner:
                    id: palette_spinner
                    text: 'Recent'
                    values: ['Recent', 'Sweetie 16', 'PICO-8']
                    size_hint_x: 0.3
                    on_text: root.load_palette(self.text)
                Button:
                    text: 'Edit Pal'
                    size_hint_x: 0.15
                    on_press: root.open_palette_creator()
                ToggleButton:
                    id: pal_lock_btn
                    text: 'Pal Lock'
                    size_hint_x: 0.2
                    background_color: (0.3, 0.6, 0.8, 1) if self.state == 'down' else (0.2, 0.2, 0.2, 1)
                    on_press: root.toggle_palette_lock()
                ScrollView:
                    do_scroll_x: True
                    do_scroll_y: False
                    size_hint_x: 0.35
                    GridLayout:
                        id: recent_colors_box
                        rows: 2
                        cols: None
                        spacing: 2
                        size_hint_x: None
                        width: self.minimum_width

            BoxLayout:
                orientation: 'horizontal'
                size_hint: 1, 0.06
                spacing: 5
                ToggleButton:
                    id: tilemap_mode_btn
                    text: 'Tilemap'
                    background_color: (0.8, 0.6, 0.2, 1) if self.state == 'down' else (0.2, 0.2, 0.2, 1)
                    on_press: root.toggle_tilemap_mode()
                Spinner:
                    id: tile_size_spinner
                    text: '16px'
                    values: ['8px', '16px', '32px']
                    size_hint_x: 0.5
                    on_text: root.set_tile_size(self.text)

            GridLayout:
                cols: 5
                rows: 1
                size_hint: 1, 0.06
                spacing: 3
                ToggleButton:
                    id: tool_brush
                    text: 'Brush (B)'
                    group: 'tools'
                    state: 'down'
                    on_press: root.set_tool('brush')
                ToggleButton:
                    id: tool_line
                    text: 'Line (L)'
                    group: 'tools'
                    on_press: root.set_tool('line')
                ToggleButton:
                    id: tool_rect
                    text: 'Rect (R)'
                    group: 'tools'
                    on_press: root.set_tool('rect')
                ToggleButton:
                    id: tool_ellipse
                    text: 'Ellips (O)'
                    group: 'tools'
                    on_press: root.set_tool('ellipse')
                ToggleButton:
                    id: tool_grad
                    text: 'Grad (U)'
                    group: 'tools'
                    on_press: root.set_tool('gradient')

            GridLayout:
                cols: 6
                rows: 1
                size_hint: 1, 0.06
                spacing: 3
                ToggleButton:
                    id: tool_select
                    text: 'Select (S)'
                    group: 'tools'
                    on_press: root.set_tool('select')
                ToggleButton:
                    id: tool_magic
                    text: 'Magic (W)'
                    group: 'tools'
                    on_press: root.set_tool('magic_wand')
                ToggleButton:
                    id: tool_fill
                    text: 'Fill (G)'
                    group: 'tools'
                    on_press: root.set_tool('fill')
                ToggleButton:
                    id: tool_picker
                    text: 'Pick (I)'
                    group: 'tools'
                    on_press: root.set_tool('picker')
                ToggleButton:
                    id: tool_eraser
                    text: 'Eraser (E)'
                    group: 'tools'
                    on_press: root.set_tool('eraser')
                ToggleButton:
                    id: tool_move
                    text: 'Move (M)'
                    group: 'tools'
                    on_press: root.set_tool('move')

            BoxLayout:
                orientation: 'horizontal'
                size_hint: 1, 0.05
                spacing: 5
                Label:
                    text: 'Brush:'
                    color: 1, 1, 1, 1
                    size_hint_x: 0.15
                Spinner:
                    id: brush_type_spinner
                    text: 'Pixel Pen'
                    values: root.brush_names
                    size_hint_x: 0.55
                    on_text: root.set_brush_type(self.text)
                Button:
                    text: 'Create'
                    size_hint_x: 0.15
                    on_press: root.open_brush_creator()
                Button:
                    text: 'Ref'
                    size_hint_x: 0.15
                    on_press: root.reload_brushes()

            BoxLayout:
                orientation: 'horizontal'
                size_hint: 1, 0.05
                spacing: 5
                Label:
                    id: size_label
                    text: 'Size: 1'
                    color: 1, 1, 1, 1
                    size_hint_x: 0.3
                Slider:
                    id: size_slider
                    min: 1
                    max: 15
                    step: 1
                    value: 1
                    size_hint_x: 0.7
                    on_value: root.update_brush_size(self.value)

            BoxLayout:
                orientation: 'horizontal'
                size_hint: 1, 0.05
                spacing: 5
                Label:
                    id: opacity_label
                    text: 'Opacity: 100%'
                    color: 1, 1, 1, 1
                    size_hint_x: 0.3
                Slider:
                    id: opacity_slider
                    min: 0.05
                    max: 1.0
                    step: 0.05
                    value: 1.0
                    size_hint_x: 0.7
                    on_value: root.update_opacity(self.value)

            BoxLayout:
                orientation: 'horizontal'
                size_hint: 1, 0.05
                spacing: 5
                Label:
                    id: tolerance_label
                    text: 'Tol: 0'
                    color: 1, 1, 1, 1
                    size_hint_x: 0.3
                Slider:
                    id: tolerance_slider
                    min: 0
                    max: 100
                    step: 1
                    value: 0
                    size_hint_x: 0.7
                    on_value: root.update_tolerance(self.value)

            BoxLayout:
                orientation: 'horizontal'
                size_hint: 1, 0.05
                spacing: 5
                Button:
                    text: 'Undo'
                    on_press: canvas_widget.undo()
                Button:
                    text: 'Redo'
                    on_press: canvas_widget.redo()
                Button:
                    text: 'Flip H'
                    on_press: canvas_widget.flip_canvas_h()
                Button:
                    text: 'Flip V'
                    on_press: canvas_widget.flip_canvas_v()
                Button:
                    text: 'Outline'
                    on_press: canvas_widget.apply_outline()
                Button:
                    text: 'Deselect'
                    on_press: canvas_widget.clear_selection()
                ToggleButton:
                    id: fill_shape_btn
                    text: 'Fill Shp'
                    size_hint_x: 0.4
                    background_color: (0.3, 0.6, 0.8, 1) if self.state == 'down' else (0.2, 0.2, 0.2, 1)

            BoxLayout:
                orientation: 'horizontal'
                size_hint: 1, 0.05
                spacing: 5
                Label:
                    text: 'Sym:'
                    color: 1, 1, 1, 1
                    size_hint_x: 0.15
                Spinner:
                    id: symmetry_spinner
                    text: 'None'
                    values: ['None', 'X-Axis', 'Y-Axis', '4-Way', '8-Way']
                    size_hint_x: 0.3
                    on_text: canvas_widget.redraw_pixels()
                Label:
                    text: 'Press:'
                    color: 1, 1, 1, 1
                    size_hint_x: 0.15
                Spinner:
                    id: pressure_spinner
                    text: 'Opacity'
                    values: ['Off', 'Size', 'Opacity']
                    size_hint_x: 0.25
                ToggleButton:
                    id: pixel_perfect_btn
                    text: 'Pix Perf'
                    size_hint_x: 0.15
                    background_color: (0.3, 0.6, 0.8, 1) if self.state == 'down' else (0.2, 0.2, 0.2, 1)

            BoxLayout:
                orientation: 'horizontal'
                size_hint: 1, 0.05
                spacing: 5
                Label:
                    text: 'Grid:'
                    color: 1, 1, 1, 1
                    size_hint_x: 0.2
                Button:
                    text: 'Canvas Sz'
                    size_hint_x: 0.3
                    on_press: root.open_canvas_size_dialog()
                Spinner:
                    id: grid_type_spinner
                    text: 'Square'
                    values: ['Square', 'Iso Grid']
                    size_hint_x: 0.25
                    on_text: canvas_widget.redraw_pixels()
                ToggleButton:
                    id: grid_toggle
                    text: 'Toggle'
                    state: 'down'
                    size_hint_x: 0.15
                    background_color: (0.3, 0.6, 0.8, 1) if self.state == 'down' else (0.2, 0.2, 0.2, 1)
                    on_press: canvas_widget.toggle_grid()
                Spinner:
                    id: export_scale_spinner
                    text: '1x'
                    values: ['1x', '2x', '4x', '8x']
                    size_hint_x: 0.1

            BoxLayout:
                orientation: 'horizontal'
                size_hint: 1, 0.05
                spacing: 5
                Label:
                    id: zoom_label
                    text: 'Zoom: 100%'
                    color: 1, 1, 1, 1
                    size_hint_x: 0.3
                Button:
                    text: '-'
                    size_hint_x: 0.15
                    on_press: canvas_widget.zoom_out()
                Button:
                    text: '+'
                    size_hint_x: 0.15
                    on_press: canvas_widget.zoom_in()
                Button:
                    text: 'Reset'
                    size_hint_x: 0.2
                    on_press: canvas_widget.zoom_reset()
                Button:
                    text: 'Invert'
                    size_hint_x: 0.2
                    on_press: canvas_widget.invert_colors()
                
            BoxLayout:
                orientation: 'horizontal'
                size_hint: 1, 0.05
                spacing: 5
                Button:
                    text: 'Clear Lyr'
                    on_press: canvas_widget.clear_canvas()
                    background_color: 0.8, 0.2, 0.2, 1
                Button:
                    text: 'Adj'
                    on_press: root.open_adjustments_dialog()
                Button:
                    text: 'New'
                    on_press: root.open_new_canvas_dialog()
                Button:
                    text: 'Import'
                    on_press: root.open_import_dialog()
                Button:
                    text: 'Save Prj'
                    on_press: root.open_save_dialog()
                Button:
                    text: 'Load Prj'
                    on_press: root.open_load_dialog()
                
            BoxLayout:
                orientation: 'horizontal'
                size_hint: 1, 0.08
                spacing: 5
                Button:
                    text: 'Save Frame PNG'
                    on_press: canvas_widget.save_png_single()
                    background_color: 0.2, 0.8, 0.2, 1
                Button:
                    text: 'Save Sheet PNG'
                    on_press: canvas_widget.save_png()
                    background_color: 0.2, 0.8, 0.2, 1

        BoxLayout:
            orientation: 'vertical'
            size_hint: 0.22, 1
            padding: 10
            spacing: 5
            Label:
                text: 'Layers'
                color: 1, 1, 1, 1
                size_hint_y: None
                height: 30
            BoxLayout:
                orientation: 'horizontal'
                size_hint_y: None
                height: 30
                Label:
                    text: 'Lyr Opacity:'
                    color: 1, 1, 1, 1
                    size_hint_x: 0.4
                Slider:
                    id: layer_opacity_slider
                    min: 0.0
                    max: 1.0
                    step: 0.05
                    value: 1.0
                    size_hint_x: 0.6
                    on_value: root.update_layer_opacity(self.value)
            ScrollView:
                size_hint: 1, 0.45
                do_scroll_x: False
                GridLayout:
                    id: layer_list
                    cols: 1
                    spacing: 2
                    size_hint_y: None
                    height: self.minimum_height
            GridLayout:
                cols: 3
                rows: 4
                size_hint_y: None
                height: 140
                spacing: 2
                Button:
                    text: 'Add Layer'
                    on_press: canvas_widget.add_layer(False)
                Button:
                    text: 'Add Group'
                    on_press: canvas_widget.add_layer(True)
                Button:
                    text: 'Duplicate'
                    on_press: canvas_widget.duplicate_layer()
                Button:
                    text: 'Delete'
                    on_press: canvas_widget.delete_active_layer()
                Button:
                    text: 'Move Up'
                    on_press: canvas_widget.move_layer(1)
                Button:
                    text: 'Move Dn'
                    on_press: canvas_widget.move_layer(-1)
                Button:
                    text: 'Merge Dn'
                    on_press: canvas_widget.merge_layer_down()
                Button:
                    text: 'Flatten'
                    on_press: canvas_widget.flatten_image()
                ToggleButton:
                    id: alpha_lock_btn
                    text: 'Lock Alpha'
                    background_color: (0.8, 0.6, 0.2, 1) if self.state == 'down' else (0.2, 0.2, 0.2, 1)
                    on_press: 
                        canvas_widget.active_layer.alpha_locked = (self.state == 'down')
                Button:
                    text: 'Shift L'
                    on_press: canvas_widget.shift_pixels(-1, 0)
                Button:
                    text: 'Shift R'
                    on_press: canvas_widget.shift_pixels(1, 0)
                Button:
                    text: 'Shift U'
                    on_press: canvas_widget.shift_pixels(0, 1)

    BoxLayout:
        orientation: 'horizontal'
        size_hint_y: 0.08
        padding: [10, 5, 10, 5]
        spacing: 10
        
        Button:
            text: 'Add Frame'
            on_press: canvas_widget.add_frame()
        Button:
            text: 'Del Frame'
            on_press: canvas_widget.delete_frame()
        Button:
            text: '< Prev'
            on_press: canvas_widget.change_frame(-1)
        Label:
            id: frame_label
            text: 'Frame 1 / 1'
            color: 1, 1, 1, 1
            size_hint_x: 0.1
        Button:
            text: 'Next >'
            on_press: canvas_widget.change_frame(1)
            
        ScrollView:
            do_scroll_x: True
            do_scroll_y: False
            size_hint_x: 0.3
            GridLayout:
                id: frame_thumbnails
                rows: 1
                cols: None
                spacing: 5
                size_hint_x: None
                width: self.minimum_width
                
        ToggleButton:
            id: onion_skin_btn
            text: 'Onion Skin'
            background_color: (0.3, 0.6, 0.8, 1) if self.state == 'down' else (0.2, 0.2, 0.2, 1)
            on_press: canvas_widget.redraw_pixels()
            
        ToggleButton:
            id: play_btn
            text: 'Play'
            background_color: (0.2, 0.8, 0.2, 1) if self.state == 'normal' else (0.8, 0.2, 0.2, 1)
            on_press: root.toggle_playback()
        Label:
            text: 'FPS:'
            color: 1, 1, 1, 1
            size_hint_x: 0.05
        Spinner:
            id: fps_spinner
            text: '12'
            values: ['1', '6', '12', '24', '30', '60']
            size_hint_x: 0.1
            
        Button:
            text: 'Export Zip'
            on_press: canvas_widget.save_png_sequence()
            background_color: 0.2, 0.6, 0.8, 1
        Button:
            text: 'Export GIF'
            on_press: canvas_widget.save_gif()
            background_color: 0.2, 0.6, 0.8, 1
"""

# ==========================================
# 8. CANVAS VIEW
# ==========================================
class PixelCanvas(Widget):
    grid_size = NumericProperty(32)
    current_color = ListProperty((1, 0, 0, 1))
    active_tool = StringProperty('brush')
    brush_type = StringProperty('Pixel Pen')
    brush_size = NumericProperty(1)
    brush_opacity = NumericProperty(1.0)
    fill_tolerance = NumericProperty(0)
    show_grid = BooleanProperty(True)
    is_tilemap_mode = BooleanProperty(False)
    tile_size = NumericProperty(16)
    is_playing = BooleanProperty(False)

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.project = ProjectDocument(self.grid_size)
        
        self.pixel_texture = Texture.create(size=(self.grid_size, self.grid_size), colorfmt='rgba')
        self.pixel_texture.mag_filter = 'nearest'
        self.onion_texture = Texture.create(size=(self.grid_size, self.grid_size), colorfmt='rgba')
        self.onion_texture.mag_filter = 'nearest'
        self.preview_texture = Texture.create(size=(self.grid_size, self.grid_size), colorfmt='rgba')
        self.preview_texture.mag_filter = 'nearest'
        
        self.composite_fbo = Fbo(size=(self.grid_size, self.grid_size), texture=Texture.create(size=(self.grid_size, self.grid_size), colorfmt='rgba'))
        self.composite_fbo.texture.mag_filter = 'nearest'
        self.use_fbo = False
        
        self.cb_ctx = RenderContext(fs=KV_CHECKERBOARD_FS, use_parent_projection=True, use_parent_modelview=True)
        with self.cb_ctx:
            self.cb_rect = Rectangle(pos=(0,0), size=(1,1))
        
        self.is_drawing = False
        self.is_moving = False
        self.move_start_pos = None
        self.stored_pixels = None
        self.last_grid_pos = None
        self.last_stamp_pos = None
        
        self.is_drawing_shape = False
        self.shape_start_pos = None
        self.preview_pixels = None
        self.preview_layer = None
        
        self.selection_mask = None
        self.is_selecting = False
        self.sel_start_pos = None
        self.sel_end_pos = None
        self.sel_dash_offset = 0
        self.sel_anim_event = None
        self.sel_min_x = 0
        self.sel_max_x = 0
        self.sel_min_y = 0
        self.sel_max_y = 0
        
        self.clipboard_pixels = None
        self.shift_line_start = None 
        
        self.scale = 1.0
        self.offset = (0, 0)
        self.is_panning = False
        self.is_space_pressed = False
        self.is_shift_pressed = False
        self.is_alt_pressed = False
        self.is_right_erasing = False
        self.pan_start_pos = None
        
        self.playback_event = None
        self.prev_tool = 'brush'
        self.prev_brush_type = 'Pixel Pen'
        
        self._cursor_redraw_trigger = Clock.create_trigger(self._redraw_cursor, 0.016)
        self._last_cursor_grid = None
        
        self.bind(pos=self.redraw_pixels, size=self.redraw_pixels)
        Window.bind(on_mouse_pos=self.on_mouse_pos)
        event_bus.bind(on_color_change=self.set_color)

    def on_mouse_pos(self, instance, pos):
        if self.collide_point(*self.to_widget(*pos)) and not self.is_playing:
            self._cursor_redraw_trigger()

    def _redraw_cursor(self, dt):
        if not self.collide_point(*self.to_widget(*Window.mouse_pos)) or self.is_playing:
            self.canvas.after.clear()
            return
        self.canvas.after.clear()
        if self.active_tool not in ['brush', 'eraser', 'picker', 'fill', 'magic_wand']:
            return
            
        mx, my = self.to_widget(*Window.mouse_pos)
        gx, gy = self.get_grid_coords(mx, my)
        if (gx, gy) == self._last_cursor_grid and not self.is_drawing:
            return
        self._last_cursor_grid = (gx, gy)
        
        pixel_w = self.width / self.grid_size
        pixel_h = self.height / self.grid_size
        
        targets = self.get_symmetry_targets(gx, gy)
        with self.canvas.after:
            Color(1, 1, 0, 0.8)
            for tx, ty in targets:
                cx = self.x + self.offset[0] + (tx + 0.5 - self.brush_size/2) * (pixel_w * self.scale)
                cy = self.y + self.offset[1] + (self.grid_size - 1 - ty + 0.5 - self.brush_size/2) * (pixel_h * self.scale)
                cw = self.brush_size * (pixel_w * self.scale)
                ch = self.brush_size * (pixel_h * self.scale)
                Line(rectangle=(cx, cy, cw, ch), width=1)

    @property
    def active_frame(self):
        return self.project.frames[self.project.active_frame_index]

    @property
    def active_layer(self):
        return self.project.active_layer

    def recalculate_composite(self):
        self.project.is_composite_dirty = True
        App.get_running_app().root.update_frame_thumbnails()

    def update_composite(self):
        if not self.project.is_composite_dirty: return
        self.project.is_composite_dirty = False
        
        self._update_dirty_textures_recursive(self.active_frame.layers)
        
        if self.needs_cpu_composite():
            self.use_fbo = False
            self.project.composite_pixels = self.project.create_empty_pixels()
            self._render_layers(self.active_frame.layers, self.project.composite_pixels)
            self.pixel_texture.blit_buffer(self.pixels_to_bytes(self.project.composite_pixels), colorfmt='rgba')
        else:
            self.use_fbo = True
            with self.composite_fbo:
                ClearColor(0, 0, 0, 0)
                ClearBuffers()
                self._draw_layers_to_fbo(self.active_frame.layers)

    def needs_cpu_composite(self, layers=None):
        if layers is None: layers = self.active_frame.layers
        for layer in layers:
            if not layer.visible: continue
            if layer.is_folder:
                if self.needs_cpu_composite(layer.children): return True
            else:
                if layer.blend_mode in ["Multiply", "Overlay"]: return True
        return False

    def _draw_layers_to_fbo(self, layers):
        for layer in layers:
            if not layer.visible or layer.opacity == 0: continue
            if layer.is_folder:
                self._draw_layers_to_fbo(layer.children)
            else:
                Color(1, 1, 1, layer.opacity)
                Rectangle(texture=layer.texture, pos=(0,0), size=(self.grid_size, self.grid_size))

    def _update_dirty_textures_recursive(self, layers):
        for layer in layers:
            if layer.is_folder:
                self._update_dirty_textures_recursive(layer.children)
            else:
                if layer.is_dirty:
                    if layer.pixels:
                        layer.texture.blit_buffer(self.pixels_to_bytes(layer.pixels), colorfmt='rgba')
                    layer.is_dirty = False

    def _render_layers(self, layers, target_composite):
        for layer in layers:
            if not layer.visible: continue
            if layer.is_folder:
                self._render_layers(layer.children, target_composite)
            else:
                if not layer.pixels or len(layer.pixels) != self.grid_size: continue
                for y in range(self.grid_size):
                    row = layer.pixels[y]
                    comp_row = target_composite[y]
                    for x in range(self.grid_size):
                        px = row[x]
                        if px[3] > 0:
                            fg = (px[0], px[1], px[2], px[3] * layer.opacity)
                            comp_row[x] = self.blend_colors(comp_row[x], fg, layer.blend_mode)

    def pixels_to_bytes(self, pixels):
        if NP_AVAILABLE:
            arr = np.asarray(pixels, dtype=np.float32)
            arr = (arr * 255.0).astype(np.uint8)
            arr = np.flipud(arr)
            return arr.tobytes()
        buf = array('B')
        for y in range(self.grid_size - 1, -1, -1):
            for px in pixels[y]:
                buf.extend((int(px[0]*255), int(px[1]*255), int(px[2]*255), int(px[3]*255)))
        return buf.tobytes()

    def toggle_playback(self, active):
        if active:
            self.is_playing = True
            try: fps = int(App.get_running_app().root.ids.fps_spinner.text)
            except ValueError: fps = 12
            self.playback_event = Clock.schedule_interval(self.advance_frame, 1.0 / fps)
        else:
            self.is_playing = False
            if self.playback_event:
                self.playback_event.cancel()
                self.playback_event = None
        self.redraw_pixels()

    def advance_frame(self, dt): self.change_frame(1)

    def add_frame(self):
        self.project.frames.append(Frame(self.grid_size))
        self.project.active_frame_index = len(self.project.frames) - 1
        self.project.active_layer = self.active_frame.layers[0]
        self.project.save_history()
        App.get_running_app().root.update_frame_ui()
        App.get_running_app().root.update_layer_ui()
        self.recalculate_composite()
        self.redraw_pixels()

    def delete_frame(self):
        if len(self.project.frames) <= 1: return
        self.project.frames.pop(self.project.active_frame_index)
        self.project.active_frame_index = max(0, self.project.active_frame_index - 1)
        self.project.active_layer = self.active_frame.layers[0]
        App.get_running_app().root.update_frame_ui()
        App.get_running_app().root.update_layer_ui()
        self.recalculate_composite()
        self.redraw_pixels()

    def change_frame(self, direction):
        new_idx = self.project.active_frame_index + direction
        if 0 <= new_idx < len(self.project.frames):
            self.project.active_frame_index = new_idx
        elif self.is_playing:
            self.project.active_frame_index = 0
        else: return
            
        self.project.active_layer = self.active_frame.layers[0]
        App.get_running_app().root.update_frame_ui()
        App.get_running_app().root.update_layer_ui()
        self.recalculate_composite()
        self.redraw_pixels()

    def add_layer(self, is_folder=False):
        new_layer = Layer(f"Layer {len(self.active_frame.layers)+1}", self.grid_size, is_folder)
        if self.active_layer.is_folder:
            self.active_layer.children.append(new_layer)
        else:
            parent, idx = self._find_parent(self.active_frame.layers, self.active_layer)
            if parent is not None: parent.insert(idx + 1, new_layer)
            else: self.active_frame.layers.append(new_layer)
        self.project.active_layer = new_layer
        App.get_running_app().root.update_layer_ui()
        self.recalculate_composite()
        self.redraw_pixels()
        self.project.save_history()

    def duplicate_layer(self):
        if self.active_layer.is_folder: return
        new_layer = Layer(f"{self.active_layer.name} copy", self.grid_size)
        new_layer.pixels = [row[:] for row in self.active_layer.pixels]
        new_layer.opacity = self.active_layer.opacity
        new_layer.blend_mode = self.active_layer.blend_mode
        new_layer.is_dirty = True
        parent, idx = self._find_parent(self.active_frame.layers, self.active_layer)
        if parent is not None: parent.insert(idx + 1, new_layer)
        else: self.active_frame.layers.append(new_layer)
        self.project.active_layer = new_layer
        App.get_running_app().root.update_layer_ui()
        self.recalculate_composite()
        self.redraw_pixels()
        self.project.save_history()

    def delete_active_layer(self):
        if len(self.active_frame.layers) <= 1 and not self.active_layer.is_folder: return
        parent, idx = self._find_parent(self.active_frame.layers, self.active_layer)
        if parent is not None:
            parent.pop(idx)
            self.project.active_layer = self.active_frame.layers[-1]
            App.get_running_app().root.update_layer_ui()
            self.recalculate_composite()
            self.redraw_pixels()
            self.project.save_history()

    def move_layer(self, direction):
        parent, idx = self._find_parent(self.active_frame.layers, self.active_layer)
        if parent is None: return
        new_idx = idx + direction
        if 0 <= new_idx < len(parent):
            parent[idx], parent[new_idx] = parent[new_idx], parent[idx]
            App.get_running_app().root.update_layer_ui()
            self.recalculate_composite()
            self.redraw_pixels()
            self.project.save_history()

    def merge_layer_down(self):
        parent, idx = self._find_parent(self.active_frame.layers, self.active_layer)
        if parent is None or idx == 0 or self.active_layer.is_folder: return
        target_layer = parent[idx - 1]
        if target_layer.is_folder: return
        for y in range(self.grid_size):
            for x in range(self.grid_size):
                fg = self.active_layer.pixels[y][x]
                if fg[3] > 0:
                    target_layer.pixels[y][x] = self.blend_colors(target_layer.pixels[y][x], fg, self.active_layer.blend_mode)
        target_layer.is_dirty = True
        self.delete_active_layer()

    def flatten_image(self):
        flat_pixels = self.project.create_empty_pixels()
        self._render_layers(self.active_frame.layers, flat_pixels)
        for layer in self.active_frame.layers[:]:
            self.active_frame.layers.remove(layer)
        new_bg = Layer("Flattened", self.grid_size)
        new_bg.pixels = flat_pixels
        new_bg.is_dirty = True
        self.active_frame.layers.append(new_bg)
        self.project.active_layer = new_bg
        App.get_running_app().root.update_layer_ui()
        self.recalculate_composite()
        self.redraw_pixels()
        self.project.save_history()

    def _find_parent(self, search_list, layer):
        for i, l in enumerate(search_list):
            if l == layer: return search_list, i
            if l.is_folder:
                res = self._find_parent(l.children, layer)
                if res[0] is not None: return res
        return None, -1

    def undo(self): 
        self.project.undo()
        App.get_running_app().root.update_layer_ui()
        self.redraw_pixels()

    def redo(self): 
        self.project.redo()
        App.get_running_app().root.update_layer_ui()
        self.redraw_pixels()

    def clear_selection(self):
        self.selection_mask = None
        self.sel_start_pos = None
        self.sel_end_pos = None
        self.stop_selection_anim()
        self.redraw_pixels()

    def select_all(self):
        self.selection_mask = [[True for _ in range(self.grid_size)] for _ in range(self.grid_size)]
        self._update_sel_bounds()
        self.start_selection_anim()
        self.redraw_pixels()

    def invert_selection(self):
        if not self.selection_mask: self.select_all()
        else:
            self.selection_mask = [[not self.selection_mask[y][x] for x in range(self.grid_size)] for y in range(self.grid_size)]
            self._update_sel_bounds()
            self.start_selection_anim()
            self.redraw_pixels()

    def magic_wand_select(self, x, y):
        target_color = self.active_layer.pixels[y][x]
        tol = self.fill_tolerance / 255.0 * 3 
        def is_similar(c1, c2):
            if c1 == c2: return True
            if c1[3] == 0 and c2[3] != 0: return False
            if c2[3] == 0 and c1[3] != 0: return False
            return abs(c1[0]-c2[0]) + abs(c1[1]-c2[1]) + abs(c1[2]-c2[2]) <= tol

        mask = [[False for _ in range(self.grid_size)] for _ in range(self.grid_size)]
        stack = [(x, y)]
        while stack:
            cx, cy = stack.pop()
            if cx < 0 or cx >= self.grid_size or cy < 0 or cy >= self.grid_size: continue
            if mask[cy][cx]: continue
            if not is_similar(self.active_layer.pixels[cy][cx], target_color): continue
            mask[cy][cx] = True
            stack.append((cx + 1, cy)); stack.append((cx - 1, cy))
            stack.append((cx, cy + 1)); stack.append((cx, cy - 1))
        self.selection_mask = mask
        self._update_sel_bounds()
        self.start_selection_anim()
        self.redraw_pixels()

    def flip_selection_h(self):
        if not self.selection_mask or self.active_layer.is_folder: return
        xs = [x for x in range(self.grid_size) if any(self.selection_mask[y][x] for y in range(self.grid_size))]
        if not xs: return
        min_x, max_x = min(xs), max(xs)
        for y in range(self.grid_size):
            row_slice = [self.active_layer.pixels[y][x] if self.selection_mask[y][x] else None for x in range(min_x, max_x + 1)]
            row_slice.reverse()
            for i, x in enumerate(range(min_x, max_x + 1)):
                if row_slice[i] is not None:
                    self.active_layer.pixels[y][x] = row_slice[i]
        self.active_layer.is_dirty = True
        self.recalculate_composite()
        self.redraw_pixels()
        self.project.save_history()

    def flip_selection_v(self):
        if not self.selection_mask or self.active_layer.is_folder: return
        ys = [y for y in range(self.grid_size) if any(self.selection_mask[y])]
        if not ys: return
        min_y, max_y = min(ys), max(ys)
        for x in range(self.grid_size):
            col_slice = [self.active_layer.pixels[y][x] if self.selection_mask[y][x] else None for y in range(min_y, max_y + 1)]
            col_slice.reverse()
            for i, y in enumerate(range(min_y, max_y + 1)):
                if col_slice[i] is not None:
                    self.active_layer.pixels[y][x] = col_slice[i]
        self.active_layer.is_dirty = True
        self.recalculate_composite()
        self.redraw_pixels()
        self.project.save_history()

    def create_selection_mask(self, x0, y0, x1, y1):
        mask = [[False for _ in range(self.grid_size)] for _ in range(self.grid_size)]
        min_x, max_x = min(x0, x1), max(x0, x1)
        min_y, max_y = min(y0, y1), max(y0, y1)
        for y in range(min_y, max_y + 1):
            for x in range(min_x, max_x + 1):
                if 0 <= x < self.grid_size and 0 <= y < self.grid_size:
                    mask[y][x] = True
        self._update_sel_bounds()
        self.start_selection_anim()
        return mask

    def _update_sel_bounds(self):
        self.sel_min_x, self.sel_max_x = self.grid_size, 0
        self.sel_min_y, self.sel_max_y = self.grid_size, 0
        for y in range(self.grid_size):
            for x in range(self.grid_size):
                if self.selection_mask[y][x]:
                    self.sel_min_x = min(self.sel_min_x, x)
                    self.sel_max_x = max(self.sel_max_x, x)
                    self.sel_min_y = min(self.sel_min_y, y)
                    self.sel_max_y = max(self.sel_max_y, y)

    def copy_selection(self):
        if not self.selection_mask: return
        self.clipboard_pixels = [[self.active_layer.pixels[y][x] if self.selection_mask[y][x] else (0,0,0,0) for x in range(self.grid_size)] for y in range(self.grid_size)]

    def cut_selection(self):
        if not self.selection_mask: return
        self.copy_selection()
        for y in range(self.grid_size):
            for x in range(self.grid_size):
                if self.selection_mask[y][x]:
                    self.active_layer.pixels[y][x] = (0, 0, 0, 0)
        self.active_layer.is_dirty = True
        self.recalculate_composite()
        self.redraw_pixels()
        self.project.save_history()

    def paste_selection(self):
        if not self.clipboard_pixels: return
        self.add_layer(False)
        self.active_layer.pixels = [row[:] for row in self.clipboard_pixels]
        self.active_layer.name = "Pasted"
        self.active_layer.is_dirty = True
        self.selection_mask = [[p[3] > 0 for p in row] for row in self.clipboard_pixels]
        self._update_sel_bounds()
        self.start_selection_anim()
        App.get_running_app().root.set_tool('move')
        App.get_running_app().root.update_tool_buttons()
        self.recalculate_composite()
        self.redraw_pixels()
        self.project.save_history()

    def duplicate_selection(self):
        if not self.selection_mask: return
        self.copy_selection()
        self.paste_selection()
        
    def start_selection_anim(self):
        if not self.sel_anim_event:
            self.sel_anim_event = Clock.schedule_interval(self.update_selection_anim, 0.1)
            
    def update_selection_anim(self, dt):
        self.sel_dash_offset = (self.sel_dash_offset + 1) % 8
        self.redraw_pixels()
        
    def stop_selection_anim(self):
        if self.sel_anim_event:
            self.sel_anim_event.cancel()
            self.sel_anim_event = None

    def on_touch_down(self, touch):
        if self.is_playing: return 
        if self.collide_point(*touch.pos):
            if self.is_space_pressed or touch.button == 'middle':
                self.is_panning = True
                self.pan_start_pos = (touch.x - self.offset[0], touch.y - self.offset[1])
                return True

            if touch.button == 'right':
                self.is_right_erasing = True
                self.is_drawing = True
                self.last_grid_pos = None
                self.last_stamp_pos = None
                self.handle_touch(touch.x, touch.y, touch.pressure if hasattr(touch, 'pressure') else 1.0)
                return True
                
            if touch.is_mouse_scrolling:
                if touch.button == 'scrolldown': self.zoom_out(touch.x, touch.y)
                elif touch.button == 'scrollup': self.zoom_in(touch.x, touch.y)
                return True

            grid_x, grid_y = self.get_grid_coords(touch.x, touch.y)
                
            if self.is_alt_pressed:
                picked_color = self.project.composite_pixels[grid_y][grid_x] if not self.use_fbo else self.get_fbo_pixel(grid_x, grid_y)
                if picked_color != (0, 0, 0, 0): event_bus.broadcast_color(picked_color)
                return True

            if self.active_tool == 'magic_wand' and touch.button == 'left':
                self.magic_wand_select(grid_x, grid_y)
                return True

            if self.active_tool == 'brush' and self.is_shift_pressed:
                if self.shift_line_start:
                    points = self.get_bresenham_line(self.shift_line_start[0], self.shift_line_start[1], grid_x, grid_y)
                    for px, py in points:
                        self.apply_tool_at(px, py, is_move=False, pressure=1.0)
                    self.shift_line_start = (grid_x, grid_y)
                else:
                    self.apply_tool_at(grid_x, grid_y, is_move=False, pressure=1.0)
                    self.shift_line_start = (grid_x, grid_y)
                self.active_layer.is_dirty = True
                self.recalculate_composite()
                self.redraw_pixels()
                self.project.save_history()
                return True

            if self.active_tool == 'move':
                self.is_moving = True
                self.move_start_pos = grid_x, grid_y
                self.stored_pixels = [row[:] for row in self.active_layer.pixels]
                return True
            elif self.active_tool in ['line', 'rect', 'ellipse', 'gradient']:
                self.is_drawing_shape = True
                self.shape_start_pos = grid_x, grid_y
                self.update_shape_preview(touch.x, touch.y)
                return True
            elif self.active_tool == 'select':
                self.is_selecting = True
                self.sel_start_pos = grid_x, grid_y
                self.sel_end_pos = grid_x, grid_y
                return True
            else:
                self.is_drawing = True
                self.last_grid_pos = None
                self.last_stamp_pos = None
                self.handle_touch(touch.x, touch.y, touch.pressure if hasattr(touch, 'pressure') else 1.0)
                return True
        else:
            if self.selection_mask: self.clear_selection()
                
        return super().on_touch_down(touch)

    def get_fbo_pixel(self, x, y):
        tex = self.composite_fbo.texture
        data = tex.pixels
        idx = ((self.grid_size - 1 - y) * self.grid_size + x) * 4
        r, g, b, a = data[idx], data[idx+1], data[idx+2], data[idx+3]
        return (r/255.0, g/255.0, b/255.0, a/255.0)

    def on_touch_move(self, touch):
        if self.is_panning:
            self.offset = (touch.x - self.pan_start_pos[0], touch.y - self.pan_start_pos[1])
            self.redraw_pixels()
            return True
            
        if self.is_moving and self.collide_point(*touch.pos):
            curr_x, curr_y = self.get_grid_coords(touch.x, touch.y)
            dx = curr_x - self.move_start_pos[0]
            dy = curr_y - self.move_start_pos[1]
            self.active_layer.pixels = self.project.create_empty_pixels()
            for y in range(self.grid_size):
                for x in range(self.grid_size):
                    nx, ny = x - dx, y - dy
                    if 0 <= nx < self.grid_size and 0 <= ny < self.grid_size:
                        if not self.selection_mask or self.selection_mask[ny][nx]:
                            self.active_layer.pixels[y][x] = self.stored_pixels[ny][nx]
            self.active_layer.is_dirty = True
            self.recalculate_composite()
            self.redraw_pixels()
            return True
            
        if self.is_drawing_shape and self.collide_point(*touch.pos):
            self.update_shape_preview(touch.x, touch.y)
            return True
            
        if self.is_selecting and self.collide_point(*touch.pos):
            self.sel_end_pos = self.get_grid_coords(touch.x, touch.y)
            self.redraw_pixels()
            return True
            
        if self.is_drawing and self.collide_point(*touch.pos):
            self.handle_touch(touch.x, touch.y, touch.pressure if hasattr(touch, 'pressure') else 1.0, is_move=True)
            return True
        return super().on_touch_move(touch)

    def on_touch_up(self, touch):
        if self.is_panning: self.is_panning = False
        if self.is_moving:
            self.is_moving = False
            self.move_start_pos = None
            self.stored_pixels = None
            self.project.save_history()
        if self.is_drawing_shape:
            self.is_drawing_shape = False
            if not self.shape_start_pos: return
                
            curr_x, curr_y = self.get_grid_coords(touch.x, touch.y)
            
            if self.is_alt_pressed:
                cx_s, cy_s = self.shape_start_pos
                curr_x = cx_s + (cx_s - curr_x)
                curr_y = cy_s + (cy_s - curr_y)
            
            if self.is_shift_pressed:
                if self.active_tool == 'line':
                    dx = curr_x - self.shape_start_pos[0]
                    dy = curr_y - self.shape_start_pos[1]
                    if dx != 0 or dy != 0:
                        angle = math.atan2(dy, dx)
                        angle = round(angle / (math.pi / 4)) * (math.pi / 4)
                        dist = round(math.hypot(dx, dy))
                        curr_x = self.shape_start_pos[0] + round(math.cos(angle) * dist)
                        curr_y = self.shape_start_pos[1] + round(math.sin(angle) * dist)
                elif self.active_tool in ['rect', 'ellipse']:
                    dx = curr_x - self.shape_start_pos[0]
                    dy = curr_y - self.shape_start_pos[1]
                    size = max(abs(dx), abs(dy))
                    curr_x = self.shape_start_pos[0] + (size if dx > 0 else -size)
                    curr_y = self.shape_start_pos[1] + (size if dy > 0 else -size)
            
            fill_shapes = App.get_running_app().root.ids.fill_shape_btn.state == 'down'
            points = []
            
            if self.active_tool == 'line':
                points = self.get_bresenham_line(self.shape_start_pos[0], self.shape_start_pos[1], curr_x, curr_y)
            elif self.active_tool == 'rect':
                points = self.get_rect_points(self.shape_start_pos[0], self.shape_start_pos[1], curr_x, curr_y, fill_shapes)
            elif self.active_tool == 'ellipse':
                points = self.get_ellipse_points(self.shape_start_pos[0], self.shape_start_pos[1], curr_x, curr_y, fill_shapes)
            elif self.active_tool == 'gradient':
                self.preview_layer = Layer("Preview", self.grid_size)
                self.draw_gradient(self.shape_start_pos[0], self.shape_start_pos[1], curr_x, curr_y)
                for y in range(self.grid_size):
                    for x in range(self.grid_size):
                        if self.preview_layer.pixels[y][x][3] > 0:
                            self.active_layer.pixels[y][x] = self.blend_colors(self.active_layer.pixels[y][x], self.preview_layer.pixels[y][x])
            
            for px, py in points:
                self.apply_tool_at(px, py, is_move=False, pressure=1.0)
                
            self.preview_pixels = None
            self.shape_start_pos = None
            self.active_layer.is_dirty = True
            self.recalculate_composite()
            self.redraw_pixels()
            self.project.save_history()
            
        if self.is_selecting:
            self.is_selecting = False
            if self.sel_start_pos and self.sel_end_pos:
                self.selection_mask = self.create_selection_mask(self.sel_start_pos[0], self.sel_start_pos[1], self.sel_end_pos[0], self.sel_end_pos[1])
            self.redraw_pixels()
            
        if self.is_drawing:
            self.is_drawing = False
            self.last_grid_pos = None
            self.last_stamp_pos = None
            self.project.save_history()

        if self.is_right_erasing: self.is_right_erasing = False

    def get_grid_coords(self, x, y):
        cx = (x - self.x - self.offset[0]) / self.scale
        cy = (y - self.y - self.offset[1]) / self.scale
        pixel_w = self.width / self.grid_size
        pixel_h = self.height / self.grid_size
        grid_x = int(cx / pixel_w)
        grid_y = int(cy / pixel_h)
        grid_x = max(0, min(self.grid_size - 1, grid_x))
        grid_y = max(0, min(self.grid_size - 1, grid_y))
        return grid_x, self.grid_size - 1 - grid_y

    def handle_touch(self, x, y, pressure=1.0, is_move=False):
        arr_x, arr_y = self.get_grid_coords(x, y)

        if self.is_tilemap_mode:
            tile_x = arr_x // self.tile_size
            tile_y = arr_y // self.tile_size
            if self.active_tool == 'picker': return self.pick_tile(tile_x, tile_y)
            elif self.active_tool == 'fill' and not is_move:
                self.tile_flood_fill(tile_x, tile_y)
                self.active_layer.is_dirty = True
                self.recalculate_composite()
                self.redraw_pixels()
                return
            elif self.active_tool in ['brush', 'eraser']:
                if self.last_grid_pos:
                    last_tx = self.last_grid_pos[0] // self.tile_size
                    last_ty = self.last_grid_pos[1] // self.tile_size
                    points = self.get_bresenham_line(last_tx, last_ty, tile_x, tile_y)
                    for px, py in points: self.apply_tile_tool_at(px, py)
                else: self.apply_tile_tool_at(tile_x, tile_y)
                self.last_grid_pos = (arr_x, arr_y)
                self.active_layer.is_dirty = True
                self.recalculate_composite()
                self.redraw_pixels()
                return

        if self.active_tool == 'picker' and not is_move:
            picked_color = self.project.composite_pixels[arr_y][arr_x] if not self.use_fbo else self.get_fbo_pixel(arr_x, arr_y)
            if picked_color != (0, 0, 0, 0): event_bus.broadcast_color(picked_color)
            App.get_running_app().root.set_tool(self.prev_tool)
            if self.prev_brush_type: App.get_running_app().root.set_brush_type(self.prev_brush_type)
            return
        elif self.active_tool == 'fill' and not is_move:
            target_color = self.active_layer.pixels[arr_y][arr_x]
            replacement_color = (*self.current_color[:3], self.current_color[3] * self.brush_opacity)
            self.flood_fill(arr_x, arr_y, target_color, replacement_color)
            self.active_layer.is_dirty = True
            self.recalculate_composite()
            self.redraw_pixels()
            return

        if self.last_grid_pos:
            points = self.get_bresenham_line(self.last_grid_pos[0], self.last_grid_pos[1], arr_x, arr_y)
            for px, py in points: self.apply_tool_at(px, py, is_move, pressure)
        else: self.apply_tool_at(arr_x, arr_y, is_move, pressure)

        self.last_grid_pos = (arr_x, arr_y)
        self.active_layer.is_dirty = True
        self.recalculate_composite()
        self.redraw_pixels()

    def get_symmetry_targets(self, cx, cy):
        S = self.grid_size
        mode = App.get_running_app().root.ids.symmetry_spinner.text
        targets = set()
        targets.add((cx, cy))
        if mode == 'X-Axis': targets.add((S - 1 - cx, cy))
        elif mode == 'Y-Axis': targets.add((cx, S - 1 - cy))
        elif mode == '4-Way':
            targets.add((S - 1 - cx, cy))
            targets.add((cx, S - 1 - cy))
            targets.add((S - 1 - cx, S - 1 - cy))
        elif mode == '8-Way':
            targets.add((S - 1 - cx, cy))
            targets.add((cx, S - 1 - cy))
            targets.add((S - 1 - cx, S - 1 - cy))
            targets.add((cy, cx))
            targets.add((S - 1 - cy, cx))
            targets.add((cy, S - 1 - cx))
            targets.add((S - 1 - cy, S - 1 - cx))
        return list(targets)

    def get_bresenham_line(self, x0, y0, x1, y1, pixel_perfect=False):
        points = []
        dx = abs(x1 - x0)
        dy = abs(y1 - y0)
        sx = 1 if x0 < x1 else -1
        sy = 1 if y0 < y1 else -1
        err = dx - dy
        while True:
            points.append((x0, y0))
            if x0 == x1 and y0 == y1: break
            e2 = 2 * err
            if e2 > -dy: err -= dy; x0 += sx
            if e2 < dx: err += dx; y0 += sy

        if pixel_perfect and len(points) >= 3:
            cleaned = points[:2]
            for i in range(2, len(points)):
                p_prev = cleaned[-2]
                p_curr = cleaned[-1]
                p_next = points[i]
                # If p_prev to p_next is a diagonal step
                if p_next[0] != p_prev[0] and p_next[1] != p_prev[1]:
                    # If p_curr is the orthogonal connector
                    if (p_curr[0] == p_prev[0] and p_curr[1] == p_next[1]) or \
                       (p_curr[1] == p_prev[1] and p_curr[0] == p_next[0]):
                        cleaned.pop() # Remove corner
                cleaned.append(p_next)
            points = cleaned
        return points

    def get_rect_points(self, x0, y0, x1, y1, fill=False):
        points = set()
        min_x, max_x = min(x0, x1), max(x0, x1)
        min_y, max_y = min(y0, y1), max(y0, y1)
        if fill:
            for y in range(min_y, max_y + 1):
                for x in range(min_x, max_x + 1): points.add((x, y))
        else:
            for x in range(min_x, max_x + 1):
                points.add((x, min_y))
                points.add((x, max_y))
            for y in range(min_y, max_y + 1):
                points.add((min_x, y))
                points.add((max_x, y))
        return list(points)

    def get_ellipse_points(self, x0, y0, x1, y1, fill=False):
        xc = (x0 + x1) // 2
        yc = (y0 + y1) // 2
        rx = abs(x1 - x0) // 2
        ry = abs(y1 - y0) // 2
        points = set()
        if rx == 0 or ry == 0: return self.get_rect_points(x0, y0, x1, y1, fill)
            
        if fill:
            for y in range(-ry, ry + 1):
                val = 1.0 - (y*y) / float(ry*ry)
                if val < 0: continue
                x_extent = int(round(rx * math.sqrt(val)))
                for x in range(-x_extent, x_extent + 1): points.add((x + xc, y + yc))
        else:
            x = 0
            y = ry
            d1 = (ry * ry) - (rx * rx * ry) + (0.25 * rx * rx)
            dx = 2 * ry * ry * x
            dy = 2 * rx * rx * y
            while dx < dy:
                points.add((x + xc, y + yc))
                points.add((-x + xc, y + yc))
                points.add((x + xc, -y + yc))
                points.add((-x + xc, -y + yc))
                if d1 < 0:
                    x += 1
                    dx = dx + (2 * ry * ry)
                    d1 = d1 + dx + (ry * ry)
                else:
                    x += 1
                    y -= 1
                    dx = dx + (2 * ry * ry)
                    dy = dy - (2 * rx * rx)
                    d1 = d1 + dx - dy + (ry * ry)
            d2 = (((ry * ry) * ((x + 0.5) * (x + 0.5))) + 
                  ((rx * rx) * ((y - 1) * (y - 1))) - 
                  (rx * rx * ry * ry))
            while y >= 0:
                points.add((x + xc, y + yc))
                points.add((-x + xc, y + yc))
                points.add((x + xc, -y + yc))
                points.add((-x + xc, -y + yc))
                if d2 > 0:
                    y -= 1
                    dy = dy - (2 * rx * rx)
                    d2 = d2 + (rx * rx) - dy
                else:
                    y -= 1
                    x += 1
                    dx = dx + (2 * ry * ry)
                    dy = dy - (2 * rx * rx)
                    d2 = d2 + dx - dy + (rx * rx)
        return list(points)

    def draw_gradient(self, x0, y0, x1, y1):
        if not self.preview_layer: return
        dx = x1 - x0
        dy = y1 - y0
        dist = math.hypot(dx, dy)
        if dist == 0: return
        base_rgb = self.current_color[:3]
        base_opacity = self.current_color[3] * self.brush_opacity
        
        for y in range(self.grid_size):
            for x in range(self.grid_size):
                if self.selection_mask and not self.selection_mask[y][x]: continue
                t = ((x - x0) * dx + (y - y0) * dy) / (dist * dist)
                t = max(0.0, min(1.0, t))
                fg = (*base_rgb, base_opacity * (1.0 - t))
                if t < 1.0:
                    self.preview_layer.pixels[y][x] = self.blend_colors(self.preview_layer.pixels[y][x], fg)

    def update_shape_preview(self, x, y):
        curr_x, curr_y = self.get_grid_coords(x, y)
        if self.is_alt_pressed:
            cx_s, cy_s = self.shape_start_pos
            curr_x = cx_s + (cx_s - curr_x)
            curr_y = cy_s + (cy_s - curr_y)
            
        if self.is_shift_pressed:
            if self.active_tool == 'line':
                dx = curr_x - self.shape_start_pos[0]
                dy = curr_y - self.shape_start_pos[1]
                if dx != 0 or dy != 0:
                    angle = math.atan2(dy, dx)
                    angle = round(angle / (math.pi / 4)) * (math.pi / 4)
                    dist = round(math.hypot(dx, dy))
                    curr_x = self.shape_start_pos[0] + round(math.cos(angle) * dist)
                    curr_y = self.shape_start_pos[1] + round(math.sin(angle) * dist)
            elif self.active_tool in ['rect', 'ellipse']:
                dx = curr_x - self.shape_start_pos[0]
                dy = curr_y - self.shape_start_pos[1]
                size = max(abs(dx), abs(dy))
                curr_x = self.shape_start_pos[0] + (size if dx > 0 else -size)
                curr_y = self.shape_start_pos[1] + (size if dy > 0 else -size)
                
        fill_shapes = App.get_running_app().root.ids.fill_shape_btn.state == 'down'
        self.preview_layer = Layer("Preview", self.grid_size)
        points = []
        
        if self.active_tool == 'line': points = self.get_bresenham_line(self.shape_start_pos[0], self.shape_start_pos[1], curr_x, curr_y)
        elif self.active_tool == 'rect': points = self.get_rect_points(self.shape_start_pos[0], self.shape_start_pos[1], curr_x, curr_y, fill_shapes)
        elif self.active_tool == 'ellipse': points = self.get_ellipse_points(self.shape_start_pos[0], self.shape_start_pos[1], curr_x, curr_y, fill_shapes)
        elif self.active_tool == 'gradient': self.draw_gradient(self.shape_start_pos[0], self.shape_start_pos[1], curr_x, curr_y)
        else: return
            
        orig_layer = self.project.active_layer
        self.project.active_layer = self.preview_layer
        for px, py in points: self.apply_tool_at(px, py, is_move=False, pressure=1.0)
        self.project.active_layer = orig_layer
        
        self.preview_pixels = self.preview_layer.pixels
        self.redraw_pixels()

    def apply_tile_tool_at(self, tx, ty):
        if self.active_layer.is_folder: return
        if self.active_tool == 'brush' or self.is_right_erasing: self.stamp_tile(tx, ty)
        elif self.active_tool == 'eraser': self.erase_tile(tx, ty)

    def get_tile_composite(self, frame):
        temp_composite = self.project.create_empty_pixels()
        self._render_layers(frame.layers, temp_composite)
        return temp_composite

    def get_tile_hash(self, pixels):
        return hash(tuple(tuple(row) for row in pixels))

    def stamp_tile(self, tx, ty, replace=False):
        tile_composite = self.get_tile_composite(self.active_frame)
        for dy in range(self.tile_size):
            for dx in range(self.tile_size):
                px = tx * self.tile_size + dx
                py = ty * self.tile_size + dy
                if 0 <= px < self.grid_size and 0 <= py < self.grid_size:
                    stamp_px = tile_composite[dy][dx]
                    if replace: self.active_layer.pixels[py][px] = stamp_px
                    else:
                        if stamp_px[3] > 0:
                            self.active_layer.pixels[py][px] = self.blend_colors(self.active_layer.pixels[py][px], stamp_px)

    def erase_tile(self, tx, ty):
        for dy in range(self.tile_size):
            for dx in range(self.tile_size):
                px = tx * self.tile_size + dx
                py = ty * self.tile_size + dy
                if 0 <= px < self.grid_size and 0 <= py < self.grid_size:
                    self.active_layer.pixels[py][px] = (0, 0, 0, 0)

    def pick_tile(self, tx, ty):
        clicked_hash = self.get_tile_hash(
            [row[tx*self.tile_size:(tx+1)*self.tile_size] for row in self.active_layer.pixels[ty*self.tile_size:(ty+1)*self.tile_size]]
        )
        for i, frame in enumerate(self.project.frames):
            tile_hash = self.get_tile_hash(
                [row[0:self.tile_size] for row in self.get_tile_composite(frame)[0:self.tile_size]]
            )
            if clicked_hash == tile_hash:
                self.project.active_frame_index = i
                self.project.active_layer = self.active_frame.layers[0]
                App.get_running_app().root.update_frame_ui()
                App.get_running_app().root.update_layer_ui()
                return

    def tile_flood_fill(self, tx, ty):
        target_hash = self.get_tile_hash(
            [row[tx*self.tile_size:(tx+1)*self.tile_size] for row in self.active_layer.pixels[ty*self.tile_size:(ty+1)*self.tile_size]]
        )
        replacement_hash = self.get_tile_hash(
            [row[0:self.tile_size] for row in self.get_tile_composite(self.active_frame)[0:self.tile_size]]
        )
        if target_hash == replacement_hash: return
        stack = [(tx, ty)]
        max_tx = self.grid_size // self.tile_size
        max_ty = self.grid_size // self.tile_size
        while stack:
            cx, cy = stack.pop()
            if cx < 0 or cx >= max_tx or cy < 0 or cy >= max_ty: continue
            curr_hash = self.get_tile_hash(
                [row[cx*self.tile_size:(cx+1)*self.tile_size] for row in self.active_layer.pixels[cy*self.tile_size:(cy+1)*self.tile_size]]
            )
            if curr_hash != target_hash: continue
            self.stamp_tile(cx, cy, replace=True)
            stack.append((cx + 1, cy)); stack.append((cx - 1, cy))
            stack.append((cx, cy + 1)); stack.append((cx, cy - 1))

    def apply_tool_at(self, cx, cy, is_move=False, pressure=1.0):
        if self.active_layer.is_folder: return
        current_tool = 'eraser' if self.is_right_erasing else self.active_tool
        
        pressure = max(0.0, min(1.0, pressure))
        pressure_mode = App.get_running_app().root.ids.pressure_spinner.text
        eff_size = self.brush_size
        eff_opacity = self.brush_opacity
        
        if pressure_mode == 'Size': eff_size = max(1, int(self.brush_size * pressure))
        elif pressure_mode == 'Opacity': eff_opacity = self.brush_opacity * pressure
            
        if current_tool in ['brush', 'line', 'rect', 'ellipse', 'gradient']:
            brush_def = App.get_running_app().root.get_active_brush_def()
            spacing_mult = brush_def.get('spacing', 0.1)
            spacing_dist = max(1, int(eff_size * spacing_mult))
            if is_move and self.last_stamp_pos:
                dist = abs(cx - self.last_stamp_pos[0]) + abs(cy - self.last_stamp_pos[1])
                if dist < spacing_dist: return
            self.paint_brush(cx, cy, brush_def, eff_size, eff_opacity)
            self.last_stamp_pos = (cx, cy)
        elif current_tool == 'eraser': self.erase_brush(cx, cy, eff_size, eff_opacity)

    def blend_colors(self, bg, fg, blend_mode="Normal"):
        bg_a = bg[3]
        fg_a = fg[3]
        if bg_a == 0: return fg
        if fg_a == 0: return bg
        fg_r, fg_g, fg_b = fg[0], fg[1], fg[2]
        bg_r, bg_g, bg_b = bg[0], bg[1], bg[2]
        if blend_mode == "Multiply":
            fg_r, fg_g, fg_b = fg_r * bg_r, fg_g * bg_g, fg_b * bg_b
        elif blend_mode == "Add":
            fg_r, fg_g, fg_b = min(1, fg_r + bg_r), min(1, fg_g + bg_g), min(1, fg_b + bg_b)
        elif blend_mode == "Overlay":
            fg_r = 1 - 2*(1-fg_r)*(1-bg_r) if fg_r > 0.5 else 2*fg_r*bg_r
            fg_g = 1 - 2*(1-fg_g)*(1-bg_g) if fg_g > 0.5 else 2*fg_g*bg_g
            fg_b = 1 - 2*(1-fg_b)*(1-bg_b) if fg_b > 0.5 else 2*fg_b*bg_b
        out_a = fg_a + bg_a * (1 - fg_a)
        if out_a == 0: return (0, 0, 0, 0)
        inv_out_a = 1.0 / out_a
        bg_a_inv_fg = bg_a * (1 - fg_a)
        out_r = (fg_r * fg_a + bg_r * bg_a_inv_fg) * inv_out_a
        out_g = (fg_g * fg_a + bg_g * bg_a_inv_fg) * inv_out_a
        out_b = (fg_b * fg_a + bg_b * bg_a_inv_fg) * inv_out_a
        return (out_r, out_g, out_b, out_a)

    def paint_brush(self, cx, cy, brush_def, eff_size, eff_opacity):
        base_rgb = self.current_color[:3]
        opacity_mult = brush_def.get('opacity_mult', 1.0)
        blend = brush_def.get('blend', False)
        shape = brush_def.get('shape', 'square')
        hardness = brush_def.get('hardness', 1.0)
        jitter = brush_def.get('jitter', 0.0)
        size_jitter = brush_def.get('size_jitter', 0.0)
        final_opacity = eff_opacity * opacity_mult
        symmetry_targets = self.get_symmetry_targets(cx, cy)

        if shape == 'blur':
            for tx, ty in symmetry_targets:
                r_sum, g_sum, b_sum, a_sum, count = 0, 0, 0, 0, 0
                for dy in range(-eff_size, eff_size + 1):
                    for dx in range(-eff_size, eff_size + 1):
                        px, py = tx + dx, ty + dy
                        if 0 <= px < self.grid_size and 0 <= py < self.grid_size:
                            if self.selection_mask and not self.selection_mask[py][px]: continue
                            r, g, b, a = self.active_layer.pixels[py][px]
                            if a > 0:
                                r_sum += r; g_sum += g; b_sum += b; a_sum += a
                                count += 1
                if count > 0:
                    avg_color = (r_sum/count, g_sum/count, b_sum/count, a_sum/count)
                    for dy in range(-eff_size, eff_size + 1):
                        for dx in range(-eff_size, eff_size + 1):
                            px, py = tx + dx, ty + dy
                            if 0 <= px < self.grid_size and 0 <= py < self.grid_size:
                                if self.selection_mask and not self.selection_mask[py][px]: continue
                                if dx*dx + dy*dy <= eff_size*eff_size:
                                    self.active_layer.pixels[py][px] = self.blend_colors(self.active_layer.pixels[py][px], avg_color)
            return

        fg_color = (*base_rgb, final_opacity)

        for tx, ty in symmetry_targets:
            size = int(eff_size * random.uniform(1.0 - size_jitter, 1.0)) if size_jitter > 0 else eff_size
            if size < 1: size = 1
            for dy in range(-size, size + 1):
                for dx in range(-size, size + 1):
                    px, py = tx + dx, ty + dy
                    if 0 <= px < self.grid_size and 0 <= py < self.grid_size:
                        if self.selection_mask and not self.selection_mask[py][px]: continue
                        if self.active_layer.alpha_locked and self.active_layer.pixels[py][px][3] == 0: continue
                        dist = (dx*dx + dy*dy) ** 0.5
                        paint = False
                        current_fg = fg_color
                        if shape == 'square':
                            if abs(dx) <= size and abs(dy) <= size: paint = True
                        elif shape == 'circle':
                            if dist <= size:
                                if dist > size - (1.0 - hardness): current_fg = (*base_rgb, final_opacity * (size - dist))
                                paint = True
                        elif shape == 'soft_circle':
                            if dist <= size:
                                falloff = max(0, 1.0 - (dist / max(0.1, size + 0.5)))
                                current_fg = (*base_rgb, final_opacity * falloff)
                                paint = True
                        elif shape == 'scatter':
                            if dist <= size and random.random() > 0.5 + jitter*0.4: 
                                paint = True
                                if jitter > 0: current_fg = (*base_rgb, final_opacity * random.uniform(0.5, 1.0))
                        elif shape == 'noise':
                            if dist <= size and random.random() > 0.7:
                                current_fg = (*base_rgb, final_opacity * random.uniform(0.6, 1.0))
                                paint = True
                        elif shape == 'dither':
                            if (px + py) % 2 == 0 and dist <= size: paint = True
                        elif shape == 'hatch':
                            if (px - py) % 3 == 0 and dist <= size: paint = True
                        elif shape == 'hatch_cross':
                            if ((px - py) % 3 == 0 or (px + py) % 3 == 0) and dist <= size: paint = True

                        if paint:
                            new_c = self.blend_colors(self.active_layer.pixels[py][px], current_fg) if blend else current_fg
                            self.active_layer.pixels[py][px] = new_c

    def erase_brush(self, cx, cy, eff_size, eff_opacity):
        symmetry_targets = self.get_symmetry_targets(cx, cy)
        brush_def = App.get_running_app().root.get_active_brush_def()
        shape = brush_def.get('shape', 'square')
        size_jitter = brush_def.get('size_jitter', 0.0)

        for tx, ty in symmetry_targets:
            size = int(eff_size * random.uniform(1.0 - size_jitter, 1.0)) if size_jitter > 0 else eff_size
            if size < 1: size = 1
            for dy in range(-size, size + 1):
                for dx in range(-size, size + 1):
                    px, py = tx + dx, ty + dy
                    if 0 <= px < self.grid_size and 0 <= py < self.grid_size:
                        if self.selection_mask and not self.selection_mask[py][px]: continue
                        if self.active_layer.alpha_locked and self.active_layer.pixels[py][px][3] == 0: continue
                        dist = (dx*dx + dy*dy) ** 0.5
                        erase = False
                        opacity_mult = 1.0
                        if shape == 'square' or self.brush_type == 'Pixel Pen':
                            if abs(dx) <= size and abs(dy) <= size: erase = True
                        elif shape in ['circle', 'soft_circle']:
                            if dist <= size:
                                if shape == 'soft_circle': opacity_mult = max(0, 1.0 - (dist / max(0.1, size + 0.5)))
                                if opacity_mult > 0:
                                    erase = True
                                    r, g, b, a = self.active_layer.pixels[py][px]
                                    new_a = max(0, a - eff_opacity * opacity_mult)
                                    if new_a == 0: self.active_layer.pixels[py][px] = (0, 0, 0, 0)
                                    else: self.active_layer.pixels[py][px] = (r, g, b, new_a)
                        elif shape == 'scatter' or shape == 'noise':
                            if dist <= size and random.random() > 0.6: erase = True
                        if erase and shape not in ['circle', 'soft_circle']:
                            self.active_layer.pixels[py][px] = (0, 0, 0, 0)

    def flood_fill(self, x, y, target_color, replacement_color):
        if self.active_layer.alpha_locked and target_color[3] == 0: return
        stack = [(x, y)]
        tol = self.fill_tolerance / 255.0 * 3 
        def is_similar(c1, c2):
            if c1 == c2: return True
            if c1[3] == 0 and c2[3] != 0: return False
            if c2[3] == 0 and c1[3] != 0: return False
            return abs(c1[0]-c2[0]) + abs(c1[1]-c2[1]) + abs(c1[2]-c2[2]) <= tol

        while stack:
            cx, cy = stack.pop()
            if cx < 0 or cx >= self.grid_size or cy < 0 or cy >= self.grid_size: continue
            if self.selection_mask and not self.selection_mask[cy][cx]: continue
            if not is_similar(self.active_layer.pixels[cy][cx], target_color): continue
            self.active_layer.pixels[cy][cx] = replacement_color
            stack.append((cx + 1, cy)); stack.append((cx - 1, cy))
            stack.append((cx, cy + 1)); stack.append((cx, cy - 1))

    def apply_outline(self):
        if self.active_layer.is_folder: return
        outline_color = self.current_color
        old_pixels = self.active_layer.pixels
        new_pixels = [row[:] for row in old_pixels]
        
        for y in range(self.grid_size):
            for x in range(self.grid_size):
                if self.selection_mask and not self.selection_mask[y][x]: continue
                if old_pixels[y][x][3] == 0: 
                    has_opaque_neighbor = False
                    for dy in [-1, 0, 1]:
                        for dx in [-1, 0, 1]:
                            if dx == 0 and dy == 0: continue
                            nx, ny = x + dx, y + dy
                            if 0 <= nx < self.grid_size and 0 <= ny < self.grid_size:
                                if old_pixels[ny][nx][3] > 0:
                                    has_opaque_neighbor = True
                                    break
                        if has_opaque_neighbor: break
                    if has_opaque_neighbor:
                        new_pixels[y][x] = outline_color
                        
        self.active_layer.pixels = new_pixels
        self.active_layer.is_dirty = True
        self.recalculate_composite()
        self.redraw_pixels()
        self.project.save_history()

    def shift_pixels(self, dx, dy):
        if self.active_layer.is_folder: return
        old_pixels = [row[:] for row in self.active_layer.pixels]
        self.active_layer.pixels = self.project.create_empty_pixels()
        for y in range(self.grid_size):
            for x in range(self.grid_size):
                nx, ny = x - dx, y - dy
                if 0 <= nx < self.grid_size and 0 <= ny < self.grid_size:
                    if self.selection_mask and not self.selection_mask[ny][nx]: continue
                    self.active_layer.pixels[y][x] = old_pixels[ny][nx]
        self.active_layer.is_dirty = True
        self.recalculate_composite()
        self.redraw_pixels()
        self.project.save_history()

    def flip_canvas_h(self):
        for layer in self.active_frame.layers: self._flip_layer_h_recursive(layer)
        self.recalculate_composite()
        self.redraw_pixels()
        self.project.save_history()

    def flip_canvas_v(self):
        for layer in self.active_frame.layers: self._flip_layer_v_recursive(layer)
        self.recalculate_composite()
        self.redraw_pixels()
        self.project.save_history()

    def _flip_layer_h_recursive(self, layer):
        if not layer.is_folder:
            for y in range(self.grid_size): layer.pixels[y].reverse()
            layer.is_dirty = True
        else:
            for child in layer.children: self._flip_layer_h_recursive(child)

    def _flip_layer_v_recursive(self, layer):
        if not layer.is_folder:
            layer.pixels.reverse()
            layer.is_dirty = True
        else:
            for child in layer.children: self._flip_layer_v_recursive(child)

    def invert_colors(self):
        if self.active_layer.is_folder: return
        for y in range(self.grid_size):
            for x in range(self.grid_size):
                if not self.selection_mask or self.selection_mask[y][x]:
                    r, g, b, a = self.active_layer.pixels[y][x]
                    if a > 0: self.active_layer.pixels[y][x] = (1.0 - r, 1.0 - g, 1.0 - b, a)
        self.active_layer.is_dirty = True
        self.recalculate_composite()
        self.redraw_pixels()
        self.project.save_history()

    def apply_adjustments(self, h_delta, s_delta, v_delta):
        if self.active_layer.is_folder: return
        for y in range(self.grid_size):
            for x in range(self.grid_size):
                if not self.selection_mask or self.selection_mask[y][x]:
                    r, g, b, a = self.active_layer.pixels[y][x]
                    if a > 0:
                        h, s, v = colorsys.rgb_to_hsv(r, g, b)
                        h = (h + h_delta) % 1.0
                        s = max(0.0, min(1.0, s + s_delta))
                        v = max(0.0, min(1.0, v + v_delta))
                        r, g, b = colorsys.hsv_to_rgb(h, s, v)
                        self.active_layer.pixels[y][x] = (r, g, b, a)
        self.active_layer.is_dirty = True
        self.recalculate_composite()
        self.redraw_pixels()
        self.project.save_history()

    def toggle_grid(self):
        self.show_grid = not self.show_grid
        self.redraw_pixels()

    def zoom_in(self, mx=None, my=None):
        old_scale = self.scale
        self.scale = min(8.0, self.scale + 0.5)
        if mx and my:
            wx = (mx - self.offset[0]) / old_scale
            wy = (my - self.offset[1]) / old_scale
            self.offset = (mx - wx * self.scale, my - wy * self.scale)
        self.update_zoom_label()
        self.redraw_pixels()

    def zoom_out(self, mx=None, my=None):
        old_scale = self.scale
        self.scale = max(1.0, self.scale - 0.5)
        if mx and my:
            wx = (mx - self.offset[0]) / old_scale
            wy = (my - self.offset[1]) / old_scale
            self.offset = (mx - wx * self.scale, my - wy * self.scale)
        self.update_zoom_label()
        self.redraw_pixels()

    def zoom_reset(self):
        self.scale = 1.0
        self.offset = (0, 0)
        self.update_zoom_label()
        self.redraw_pixels()

    def update_zoom_label(self):
        App.get_running_app().root.ids.zoom_label.text = f"Zoom: {int(self.scale * 100)}%"

    def change_grid_size(self, size, keep_art=True):
        old_size = self.grid_size
        old_frames = self.project.frames
        self.grid_size = int(size)
        
        self.pixel_texture = Texture.create(size=(self.grid_size, self.grid_size), colorfmt='rgba')
        self.pixel_texture.mag_filter = 'nearest'
        self.onion_texture = Texture.create(size=(self.grid_size, self.grid_size), colorfmt='rgba')
        self.onion_texture.mag_filter = 'nearest'
        self.preview_texture = Texture.create(size=(self.grid_size, self.grid_size), colorfmt='rgba')
        self.preview_texture.mag_filter = 'nearest'
        
        self.composite_fbo = Fbo(size=(self.grid_size, self.grid_size), texture=Texture.create(size=(self.grid_size, self.grid_size), colorfmt='rgba'))
        self.composite_fbo.texture.mag_filter = 'nearest'
        
        for frame in old_frames:
            for layer in frame.layers:
                self._resize_layer_pixels(layer, old_size, self.grid_size, keep_art)
                layer.texture = Texture.create(size=(self.grid_size, self.grid_size), colorfmt='rgba')
                layer.texture.mag_filter = 'nearest'
                layer.is_dirty = True
                
        self.project.frames = old_frames
        self.project.grid_size = self.grid_size
        self.project.composite_pixels = self.project.create_empty_pixels()
        self.recalculate_composite()
        self.redraw_pixels()

    def _resize_layer_pixels(self, layer, old_size, new_size, keep_art):
        if layer.is_folder:
            for child in layer.children: self._resize_layer_pixels(child, old_size, new_size, keep_art)
        else:
            if not keep_art:
                layer.pixels = [[(0, 0, 0, 0) for _ in range(new_size)] for _ in range(new_size)]
                return
            new_pixels = [[(0, 0, 0, 0) for _ in range(new_size)] for _ in range(new_size)]
            copy_limit = min(old_size, new_size)
            for y in range(copy_limit):
                for x in range(copy_limit): new_pixels[y][x] = layer.pixels[y][x]
            layer.pixels = new_pixels

    def redraw_pixels(self, *args):
        if self.project.is_composite_dirty: self.update_composite()
            
        self.canvas.clear()
        pixel_w = self.width / self.grid_size
        pixel_h = self.height / self.grid_size
        
        root = App.get_running_app().root
        onion_skin_on = root.ids.onion_skin_btn.state == 'down'
        grid_type = root.ids.grid_type_spinner.text

        with self.canvas:
            self.canvas['projection_mat'] = Matrix().view(0, 0, Window.width, Window.height)
            mat = Matrix().translate(self.x + self.offset[0], self.y + self.offset[1], 0)
            mat = mat.multiply(Matrix().scale(self.scale, self.scale, 1))
            self.canvas['modelview_mat'] = mat

            self.cb_rect.pos = (0, 0)
            self.cb_rect.size = (self.width, self.height)
            self.cb_ctx['projection_mat'] = self.canvas['projection_mat']
            self.cb_ctx['modelview_mat'] = self.canvas['modelview_mat']
            self.cb_ctx.draw()

            if not self.is_playing:
                if onion_skin_on and self.project.active_frame_index > 0 and not self.is_tilemap_mode:
                    prev_frame = self.project.frames[self.project.active_frame_index - 1]
                    temp_composite = self.project.create_empty_pixels()
                    self._render_layers(prev_frame.layers, temp_composite)
                    self.onion_texture.blit_buffer(self.pixels_to_bytes(temp_composite), colorfmt='rgba')
                    Color(1, 0, 0, 0.3) 
                    Rectangle(texture=self.onion_texture, pos=(0, 0), size=(self.width, self.height))

            Color(1, 1, 1, 1)
            if self.use_fbo: Rectangle(texture=self.composite_fbo.texture, pos=(0, 0), size=(self.width, self.height))
            else: Rectangle(texture=self.pixel_texture, pos=(0, 0), size=(self.width, self.height))

            if self.preview_pixels:
                self.preview_texture.blit_buffer(self.pixels_to_bytes(self.preview_pixels), colorfmt='rgba')
                Color(1, 1, 1, 0.8)
                Rectangle(texture=self.preview_texture, pos=(0, 0), size=(self.width, self.height))

            if self.show_grid and not self.is_playing:
                Color(0.3, 0.3, 0.35, 0.5)
                if grid_type == 'Square':
                    for i in range(self.grid_size + 1):
                        Line(points=[i * pixel_w, 0, i * pixel_w, self.height], width=1)
                        Line(points=[0, i * pixel_h, self.width, i * pixel_h], width=1)
                elif grid_type == 'Iso Grid':
                    Color(0.3, 0.3, 0.35, 0.4)
                    for i in range(-self.grid_size, self.grid_size * 2):
                        start_x = i * (pixel_w / 2)
                        Line(points=[start_x, 0, start_x + self.height / 2, self.height], width=1)
                        Line(points=[start_x, self.height, start_x + self.height / 2, 0], width=1)

                if self.is_tilemap_mode:
                    Color(0.9, 0.8, 0.2, 0.8)
                    for i in range(0, self.grid_size + 1, self.tile_size):
                        Line(points=[i * pixel_w, 0, i * pixel_w, self.height], width=2)
                        Line(points=[0, i * pixel_h, self.width, i * pixel_h], width=2)
            
            if self.is_selecting and self.sel_start_pos and self.sel_end_pos:
                Color(1, 1, 1, 1)
                x0, y0 = self.sel_start_pos
                x1, y1 = self.sel_end_pos
                min_x, max_x = min(x0, x1), max(x0, x1)
                min_y, max_y = min(y0, y1), max(y0, y1)
                p1 = (min_x * pixel_w, (self.grid_size - 1 - min_y) * pixel_h)
                p2 = ((max_x + 1) * pixel_w, (self.grid_size - 1 - min_y) * pixel_h)
                p3 = ((max_x + 1) * pixel_w, (self.grid_size - 1 - max_y - 1) * pixel_h)
                p4 = (min_x * pixel_w, (self.grid_size - 1 - max_y - 1) * pixel_h)
                Line(points=[p1[0], p1[1], p2[0], p2[1], p3[0], p3[1], p4[0], p4[1], p1[0], p1[1]], width=1.5, dash_length=4, dash_offset=self.sel_dash_offset)
            elif self.selection_mask:
                Color(1, 1, 1, 1)
                p1 = (self.sel_min_x * pixel_w, (self.grid_size - 1 - self.sel_min_y) * pixel_h)
                p2 = ((self.sel_max_x + 1) * pixel_w, (self.grid_size - 1 - self.sel_min_y) * pixel_h)
                p3 = ((self.sel_max_x + 1) * pixel_w, (self.grid_size - 1 - self.sel_max_y - 1) * pixel_h)
                p4 = (self.sel_min_x * pixel_w, (self.grid_size - 1 - self.sel_max_y - 1) * pixel_h)
                Line(points=[p1[0], p1[1], p2[0], p2[1], p3[0], p3[1], p4[0], p4[1], p1[0], p1[1]], width=1.5, dash_length=4, dash_offset=self.sel_dash_offset)

            mode = root.ids.symmetry_spinner.text
            if mode != 'None' and not self.is_playing:
                Color(1, 0, 0, 0.5)
                mid_x = self.width / 2
                mid_y = self.height / 2
                if 'X' in mode or '4' in mode or '8' in mode: Line(points=[mid_x, 0, mid_x, self.height], width=1)
                if 'Y' in mode or '4' in mode or '8' in mode: Line(points=[0, mid_y, self.width, mid_y], width=1)
                if '8' in mode:
                    Line(points=[0, 0, self.width, self.height], width=1)
                    Line(points=[0, self.height, self.width, 0], width=1)

            # Tilemap Hover Highlight
            if self.is_tilemap_mode and self.collide_point(*self.to_widget(*Window.mouse_pos)) and not self.is_playing:
                mx, my = self.to_widget(*Window.mouse_pos)
                gx, gy = self.get_grid_coords(mx, my)
                tx = gx // self.tile_size
                ty = gy // self.tile_size
                Color(1, 1, 0, 0.5)
                Line(rectangle=(tx * self.tile_size * pixel_w, (self.grid_size - (ty+1)*self.tile_size) * pixel_h, 
                                self.tile_size * pixel_w, self.tile_size * pixel_h), width=2)
                    
            self.canvas['modelview_mat'] = Matrix()
            
        self._cursor_redraw_trigger()

    def clear_canvas(self):
        if not self.active_layer.is_folder:
            self.active_layer.pixels = self.project.create_empty_pixels()
            self.active_layer.is_dirty = True
            self.recalculate_composite()
            self.redraw_pixels()
            self.project.save_history()

    def save_png_single(self):
        if not PIL_AVAILABLE:
            show_error_popup("Dependency Missing", "Pillow library is not installed.\nPlease run: pip install Pillow")
            return

        content = BoxLayout(orientation='vertical', padding=10, spacing=10)
        status_label = Label(text='Initializing...', color=(1,1,1,1))
        progress_bar = ProgressBar(max=100, value=0)
        content.add_widget(status_label)
        content.add_widget(progress_bar)
        popup = Popup(title='Exporting Frame', content=content, size_hint=(0.6, 0.3), auto_dismiss=False)
        popup.open()

        def do_export():
            try:
                scale_str = App.get_running_app().root.ids.export_scale_spinner.text.replace('x', '')
                scale = int(scale_str)
                px_size = self.grid_size * scale

                def update_ui_1(dt):
                    progress_bar.value = 30
                    status_label.text = 'Rendering frame...'
                Clock.schedule_once(update_ui_1)

                temp_composite = self.project.create_empty_pixels()
                self._render_layers(self.active_frame.layers, temp_composite)
                arr = np.asarray(temp_composite, dtype=np.float32)
                arr = (arr * 255).astype(np.uint8)
                arr = np.repeat(np.repeat(arr, scale, axis=0), scale, axis=1)

                def update_ui_2(dt):
                    progress_bar.value = 80
                    status_label.text = 'Saving to disk...'
                Clock.schedule_once(update_ui_2)

                img = PILImage.fromarray(np.flipud(arr))
                filename = f"frame_{self.project.active_frame_index}_{int(time.time())}_{scale}x.png"
                img.save(filename)

                def done_ui(dt):
                    popup.dismiss()
                    show_error_popup("Success", f"Saved as {filename}")
                Clock.schedule_once(done_ui)

            except Exception as e:
                def err_ui(dt, err=e):
                    popup.dismiss()
                    show_error_popup("Save Error", f"Could not save PNG:\n{err}")
                Clock.schedule_once(err_ui)

        threading.Thread(target=do_export, daemon=True).start()

    def save_png(self):
        if not PIL_AVAILABLE:
            show_error_popup("Dependency Missing", "Pillow library is not installed.\nPlease run: pip install Pillow")
            return

        content = BoxLayout(orientation='vertical', padding=10, spacing=10)
        status_label = Label(text='Initializing...', color=(1,1,1,1))
        progress_bar = ProgressBar(max=100, value=0)
        content.add_widget(status_label)
        content.add_widget(progress_bar)
        popup = Popup(title='Exporting Spritesheet', content=content, size_hint=(0.6, 0.3), auto_dismiss=False)
        popup.open()

        def do_export():
            try:
                scale_str = App.get_running_app().root.ids.export_scale_spinner.text.replace('x', '')
                scale = int(scale_str)
                num_frames = len(self.project.frames)
                px_size = self.grid_size * scale
                total_width = px_size * num_frames
                total_height = px_size

                sheet_arr = np.zeros((total_height, total_width, 4), dtype=np.uint8)
                
                for f_idx, frame in enumerate(self.project.frames):
                    temp_composite = self.project.create_empty_pixels()
                    self._render_layers(frame.layers, temp_composite)
                    arr = np.asarray(temp_composite, dtype=np.float32)
                    arr = (arr * 255).astype(np.uint8)
                    arr = np.repeat(np.repeat(arr, scale, axis=0), scale, axis=1)
                    sheet_arr[:px_size, f_idx*px_size:(f_idx+1)*px_size] = arr
                    
                    def update_ui(dt, idx=f_idx):
                        progress_bar.value = int(((idx + 1) / num_frames) * 80)
                        status_label.text = f'Rendering frame {idx+1} / {num_frames}...'
                    Clock.schedule_once(update_ui)

                def save_ui(dt):
                    progress_bar.value = 90
                    status_label.text = 'Saving to disk...'
                Clock.schedule_once(save_ui)

                img = PILImage.fromarray(np.flipud(sheet_arr))
                filename = f"game_asset_{int(time.time())}_{num_frames}frames_{scale}x.png"
                img.save(filename)

                def done_ui(dt):
                    popup.dismiss()
                    show_error_popup("Success", f"Saved as {filename}")
                Clock.schedule_once(done_ui)

            except Exception as e:
                def err_ui(dt, err=e):
                    popup.dismiss()
                    show_error_popup("Save Error", f"Could not save PNG:\n{err}")
                Clock.schedule_once(err_ui)

        threading.Thread(target=do_export, daemon=True).start()

    def save_png_sequence(self):
        if not PIL_AVAILABLE:
            show_error_popup("Dependency Missing", "Pillow library is not installed.\nPlease run: pip install Pillow")
            return

        content = BoxLayout(orientation='vertical', padding=10, spacing=10)
        status_label = Label(text='Initializing...', color=(1,1,1,1))
        progress_bar = ProgressBar(max=100, value=0)
        content.add_widget(status_label)
        content.add_widget(progress_bar)
        popup = Popup(title='Exporting PNG Sequence', content=content, size_hint=(0.6, 0.3), auto_dismiss=False)
        popup.open()

        def do_export():
            try:
                scale_str = App.get_running_app().root.ids.export_scale_spinner.text.replace('x', '')
                scale = int(scale_str)
                px_size = self.grid_size * scale
                num_frames = len(self.project.frames)
                zip_filename = f"game_anim_{int(time.time())}_{num_frames}frames_{scale}x.zip"
                
                with zipfile.ZipFile(zip_filename, 'w', zipfile.ZIP_DEFLATED) as zf:
                    for f_idx, frame in enumerate(self.project.frames):
                        temp_composite = self.project.create_empty_pixels()
                        self._render_layers(frame.layers, temp_composite)
                        arr = np.asarray(temp_composite, dtype=np.float32)
                        arr = (arr * 255).astype(np.uint8)
                        arr = np.repeat(np.repeat(arr, scale, axis=0), scale, axis=1)
                        img = PILImage.fromarray(np.flipud(arr))
                        
                        img_bytes = io.BytesIO()
                        img.save(img_bytes, format='PNG')
                        zf.writestr(f"frame_{f_idx:04d}.png", img_bytes.getvalue())

                        def update_ui(dt, idx=f_idx):
                            progress_bar.value = int(((idx + 1) / num_frames) * 90)
                            status_label.text = f'Zipping frame {idx+1} / {num_frames}...'
                        Clock.schedule_once(update_ui)

                def done_ui(dt):
                    popup.dismiss()
                    show_error_popup("Success", f"Saved as {zip_filename}")
                Clock.schedule_once(done_ui)

            except Exception as e:
                def err_ui(dt, err=e):
                    popup.dismiss()
                    show_error_popup("Save Error", f"Could not save ZIP:\n{err}")
                Clock.schedule_once(err_ui)

        threading.Thread(target=do_export, daemon=True).start()

    def save_gif(self):
        if not PIL_AVAILABLE:
            show_error_popup("Dependency Missing", "Pillow library is not installed.\nPlease run: pip install Pillow")
            return

        content = BoxLayout(orientation='vertical', padding=10, spacing=10)
        status_label = Label(text='Initializing...', color=(1,1,1,1))
        progress_bar = ProgressBar(max=100, value=0)
        content.add_widget(status_label)
        content.add_widget(progress_bar)
        popup = Popup(title='Exporting GIF', content=content, size_hint=(0.6, 0.3), auto_dismiss=False)
        popup.open()

        def do_export():
            try:
                scale_str = App.get_running_app().root.ids.export_scale_spinner.text.replace('x', '')
                scale = int(scale_str)
                px_size = self.grid_size * scale
                fps = int(App.get_running_app().root.ids.fps_spinner.text)
                num_frames = len(self.project.frames)
                frames_pil = []
                
                for f_idx in range(num_frames):
                    temp_composite = self.project.create_empty_pixels()
                    self._render_layers(self.project.frames[f_idx].layers, temp_composite)
                    arr = np.asarray(temp_composite, dtype=np.float32)
                    arr = (arr * 255).astype(np.uint8)
                    arr = np.repeat(np.repeat(arr, scale, axis=0), scale, axis=1)
                    img = PILImage.fromarray(np.flipud(arr))
                    frames_pil.append(img)

                    def update_ui(dt, idx=f_idx):
                        progress_bar.value = int(((idx + 1) / num_frames) * 80)
                        status_label.text = f'Rendering frame {idx+1} / {num_frames}...'
                    Clock.schedule_once(update_ui)

                def save_ui(dt):
                    progress_bar.value = 90
                    status_label.text = 'Encoding GIF...'
                Clock.schedule_once(save_ui)

                filename = f"game_anim_{int(time.time())}_{num_frames}frames_{fps}fps.gif"
                frames_pil[0].save(filename, save_all=True, append_images=frames_pil[1:], duration=int(1000/fps), loop=0, disposal=2)

                def done_ui(dt):
                    popup.dismiss()
                    show_error_popup("Success", f"Saved as {filename}")
                Clock.schedule_once(done_ui)

            except Exception as e:
                def err_ui(dt, err=e):
                    popup.dismiss()
                    show_error_popup("Save Error", f"Could not save GIF:\n{err}")
                Clock.schedule_once(err_ui)

        threading.Thread(target=do_export, daemon=True).start()

# ==========================================
# 9. ROOT CONTROLLER & UI WIDGETS
# ==========================================
class LayerRow(BoxLayout):
    def __init__(self, layer, indentation, **kwargs):
        super().__init__(**kwargs)
        self.layer = layer
        self.indentation = indentation

class FrameThumbnail(Widget):
    def __init__(self, frame_idx, grid_size, **kwargs):
        super().__init__(**kwargs)
        self.frame_idx = frame_idx
        self.size_hint_x = None
        self.width = 60
        self.texture = Texture.create(size=(grid_size, grid_size), colorfmt='rgba')
        self.texture.mag_filter = 'nearest'
        self.bind(pos=self.draw, size=self.draw)

    def update_texture(self, pixels):
        if NP_AVAILABLE:
            arr = np.asarray(pixels, dtype=np.float32)
            arr = (arr * 255.0).astype(np.uint8)
            arr = np.flipud(arr)
            self.texture.blit_buffer(arr.tobytes(), colorfmt='rgba')
        else:
            buf = array('B')
            gs = self.texture.size[0]
            for y in range(gs - 1, -1, -1):
                for px in pixels[y]:
                    buf.extend((int(px[0]*255), int(px[1]*255), int(px[2]*255), int(px[3]*255)))
            self.texture.blit_buffer(buf.tobytes(), colorfmt='rgba')
        self.draw()

    def draw(self, *args):
        self.canvas.clear()
        with self.canvas:
            Color(0.2, 0.2, 0.25, 1)
            Rectangle(pos=self.pos, size=self.size)
            Color(1, 1, 1, 1)
            Rectangle(texture=self.texture, pos=self.pos, size=self.size)
            if App.get_running_app().root.ids.canvas_widget.project.active_frame_index == self.frame_idx:
                Color(0.2, 0.8, 0.2, 1)
                Line(rectangle=(self.x, self.y, self.width, self.height), width=2)

class BrushPreviewWidget(Widget):
    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.grid_size = 32
        self.pixels = [[(0,0,0,0) for _ in range(self.grid_size)] for _ in range(self.grid_size)]
        self.texture = Texture.create(size=(self.grid_size, self.grid_size), colorfmt='rgba')
        self.texture.mag_filter = 'nearest'
        self.bind(pos=self.draw, size=self.draw)

    def draw(self, *args):
        self.canvas.clear()
        with self.canvas:
            Color(0.15, 0.15, 0.18, 1)
            Rectangle(pos=self.pos, size=self.size)
            Color(1,1,1,1)
            Rectangle(texture=self.texture, pos=self.pos, size=self.size)
        
    def update_preview(self, brush_def, color, size):
        self.pixels = [[(0,0,0,0) for _ in range(self.grid_size)] for _ in range(self.grid_size)]
        x0, y0 = 8, 8
        x1, y1 = 24, 24
        dx = abs(x1 - x0); dy = abs(y1 - y0)
        sx = 1 if x0 < x1 else -1; sy = 1 if y0 < y1 else -1
        err = dx - dy
        shape = brush_def.get('shape', 'square')
        hardness = brush_def.get('hardness', 1.0)
        jitter = brush_def.get('jitter', 0.0)
        opacity_mult = brush_def.get('opacity_mult', 1.0)
        size_jitter = brush_def.get('size_jitter', 0.0)
        blend = brush_def.get('blend', False)
        eff_opacity = opacity_mult
        
        while True:
            cx, cy = x0, y0
            stamp_size = int(size * random.uniform(1.0 - size_jitter, 1.0)) if size_jitter > 0 else int(size)
            if stamp_size < 1: stamp_size = 1
            for dy_ in range(-stamp_size, stamp_size + 1):
                for dx_ in range(-stamp_size, stamp_size + 1):
                    px, py = cx + dx_, cy + dy_
                    if 0 <= px < self.grid_size and 0 <= py < self.grid_size:
                        dist = (dx_*dx_ + dy_*dy_) ** 0.5
                        paint = False
                        current_fg = (*color[:3], eff_opacity)
                        if shape == 'square':
                            if abs(dx_) <= stamp_size and abs(dy_) <= stamp_size: paint = True
                        elif shape in ['circle', 'soft_circle']:
                            if dist <= stamp_size:
                                if shape == 'soft_circle':
                                    falloff = max(0, 1.0 - (dist / max(0.1, stamp_size + 0.5)))
                                    current_fg = (*color[:3], eff_opacity * falloff)
                                elif dist > stamp_size - (1.0 - hardness):
                                    current_fg = (*color[:3], eff_opacity * (stamp_size - dist))
                                paint = True
                        elif shape == 'scatter':
                            if dist <= stamp_size and random.random() > 0.5 + jitter*0.4: 
                                paint = True
                                if jitter > 0: current_fg = (*color[:3], eff_opacity * random.uniform(0.5, 1.0))
                        elif shape == 'noise':
                            if dist <= stamp_size and random.random() > 0.7:
                                current_fg = (*color[:3], eff_opacity * random.uniform(0.6, 1.0))
                                paint = True
                        elif shape == 'dither':
                            if (px + py) % 2 == 0 and dist <= stamp_size: paint = True
                        elif shape == 'hatch':
                            if (px - py) % 3 == 0 and dist <= stamp_size: paint = True
                        elif shape == 'hatch_cross':
                            if ((px - py) % 3 == 0 or (px + py) % 3 == 0) and dist <= stamp_size: paint = True
                        if paint:
                            bg = self.pixels[py][px]
                            if bg[3] == 0: self.pixels[py][px] = current_fg
                            elif blend:
                                out_a = current_fg[3] + bg[3] * (1 - current_fg[3])
                                if out_a > 0:
                                    r = (current_fg[0]*current_fg[3] + bg[0]*bg[3]*(1-current_fg[3]))/out_a
                                    g = (current_fg[1]*current_fg[3] + bg[1]*bg[3]*(1-current_fg[3]))/out_a
                                    b = (current_fg[2]*current_fg[3] + bg[2]*bg[3]*(1-current_fg[3]))/out_a
                                    self.pixels[py][px] = (r,g,b,out_a)
            if x0 == x1 and y0 == y1: break
            e2 = 2 * err
            if e2 > -dy: err -= dy; x0 += sx
            if e2 < dx: err += dx; y0 += sy
            
        buf = array('B')
        for y in range(self.grid_size - 1, -1, -1):
            for x in range(self.grid_size):
                r, g, b, a = self.pixels[y][x]
                buf.extend([int(r*255), int(g*255), int(b*255), int(a*255)])
        self.texture.blit_buffer(bytes(buf), colorfmt='rgba')
        self.draw()

class RootWidget(BoxLayout):
    recent_colors = ListProperty([])
    brush_defs = ListProperty([])
    brush_names = ListProperty([])

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.reload_brushes()
        self.update_palette_spinner()
        self.load_palette('Recent')
        self.update_layer_ui()
        self.update_frame_ui()
        self.update_frame_thumbnails()
        Clock.schedule_interval(self.autosave, 60.0)

    def autosave(self, dt):
        try:
            tmp = 'autosave.json.tmp'
            self.save_project(tmp)
            os.replace(tmp, 'autosave.json')
        except Exception as e:
            logger.error(f"Autosave failed: {e}")

    def update_palette_spinner(self):
        self.ids.palette_spinner.values = list(PALETTES.keys())

    def reload_brushes(self):
        self.brush_defs = load_brush_packs()
        self.brush_names = [b['name'] for b in self.brush_defs]
        if self.brush_names:
            self.ids.brush_type_spinner.values = self.brush_names
            if self.ids.brush_type_spinner.text not in self.brush_names:
                self.ids.brush_type_spinner.text = self.brush_names[0]
                self.ids.canvas_widget.brush_type = self.brush_names[0]

    def get_active_brush_def(self):
        for b in self.brush_defs:
            if b['name'] == self.ids.brush_type_spinner.text: return b
        if self.brush_defs: return self.brush_defs[0]
        return {"name": "Fallback", "shape": "square", "hardness": 1.0, "jitter": 0.0, "spacing": 0.1, "size_jitter": 0.0, "blend": False, "opacity_mult": 1.0}

    def update_layer_ui(self):
        grid = self.ids.layer_list
        grid.clear_widgets()
        flat_layers = []
        self._flatten_layers(self.ids.canvas_widget.active_frame.layers, flat_layers, 0)
        for layer, indent in reversed(flat_layers):
            row = LayerRow(layer, indent)
            grid.add_widget(row)
        self.ids.layer_opacity_slider.value = self.ids.canvas_widget.active_layer.opacity
        self.ids.alpha_lock_btn.state = 'down' if self.ids.canvas_widget.active_layer.alpha_locked else 'normal'

    def update_frame_ui(self):
        cw = self.ids.canvas_widget
        prefix = "Tile" if cw.is_tilemap_mode else "Frame"
        self.ids.frame_label.text = f"{prefix} {cw.project.active_frame_index + 1} / {len(cw.project.frames)}"

    def update_frame_thumbnails(self):
        grid = self.ids.frame_thumbnails
        grid.clear_widgets()
        cw = self.ids.canvas_widget
        for i, frame in enumerate(cw.project.frames):
            temp_composite = cw.project.create_empty_pixels()
            cw._render_layers(frame.layers, temp_composite)
            thumb = FrameThumbnail(i, cw.grid_size)
            thumb.update_texture(temp_composite)
            thumb.bind(on_touch_down=self.on_thumbnail_click)
            grid.add_widget(thumb)

    def on_thumbnail_click(self, instance, touch):
        if instance.collide_point(*touch.pos):
            cw = self.ids.canvas_widget
            diff = instance.frame_idx - cw.project.active_frame_index
            if diff != 0:
                cw.change_frame(diff)

    def toggle_tilemap_mode(self):
        cw = self.ids.canvas_widget
        cw.is_tilemap_mode = not cw.is_tilemap_mode
        self.update_frame_ui()
        cw.redraw_pixels()

    def set_tile_size(self, text):
        self.ids.canvas_widget.tile_size = int(text.replace('px', ''))
        self.ids.canvas_widget.redraw_pixels()

    def toggle_playback(self):
        cw = self.ids.canvas_widget
        cw.toggle_playback(self.ids.play_btn.state == 'down')

    def toggle_palette_lock(self):
        if self.ids.pal_lock_btn.state == 'down': self.set_color(self.ids.color_wheel.color)

    def _flatten_layers(self, layers, flat_list, depth):
        for layer in layers:
            flat_list.append((layer, depth))
            if layer.is_folder: self._flatten_layers(layer.children, flat_list, depth + 1)

    def load_palette(self, name):
        box = self.ids.recent_colors_box
        box.clear_widgets()
        if name == 'Recent': colors = self.recent_colors if self.recent_colors else [(0.2,0.2,0.2,1)]
        else:
            if name not in PALETTES: return
            colors = PALETTES[name]
        for c in colors[:256]:
            btn = Button(background_color=c, size_hint_x=None, width=25)
            btn.bind(on_press=self.swatch_pressed)
            box.add_widget(btn)

    def snap_to_palette(self, color):
        palette_name = self.ids.palette_spinner.text
        if palette_name == 'Recent': return color
        palette = PALETTES[palette_name]
        if not palette: return color
        best_c = palette[0]
        best_dist = float('inf')
        for p_c in palette:
            dist = math.sqrt((color[0]-p_c[0])**2 + (color[1]-p_c[1])**2 + (color[2]-p_c[2])**2)
            if dist < best_dist:
                best_dist = dist
                best_c = p_c
        return best_c

    def set_tool(self, tool_name):
        cw = self.ids.canvas_widget
        if tool_name != 'picker' and cw.active_tool != 'picker':
            cw.prev_tool = cw.active_tool
            cw.prev_brush_type = cw.brush_type
        elif tool_name == 'picker' and cw.active_tool != 'picker':
            cw.prev_tool = cw.active_tool
            cw.prev_brush_type = cw.brush_type
        cw.active_tool = tool_name
        self.update_tool_buttons()

    def update_tool_buttons(self):
        cw = self.ids.canvas_widget
        tool = cw.active_tool
        btn_map = {
            'brush': 'tool_brush', 'line': 'tool_line', 'rect': 'tool_rect',
            'ellipse': 'tool_ellipse', 'gradient': 'tool_grad', 'select': 'tool_select',
            'fill': 'tool_fill', 'picker': 'tool_picker', 'eraser': 'tool_eraser', 
            'move': 'tool_move', 'magic_wand': 'tool_magic'
        }
        for t, btn_id in btn_map.items():
            if btn_id in self.ids: self.ids[btn_id].state = 'down' if t == tool else 'normal'

    def set_color(self, color):
        if self.ids.pal_lock_btn.state == 'down' and self.ids.palette_spinner.text != 'Recent':
            color = self.snap_to_palette(color)
        self.ids.color_wheel.color = color
        r, g, b = int(color[0]*255), int(color[1]*255), int(color[2]*255)
        self.ids.hex_input.text = f"{r:02X}{g:02X}{b:02X}"

    def apply_hex_color(self, hex_string):
        hex_string = hex_string.lstrip('#')
        if len(hex_string) == 6:
            try:
                r = int(hex_string[0:2], 16) / 255.0
                g = int(hex_string[2:4], 16) / 255.0
                b = int(hex_string[4:6], 16) / 255.0
                self.set_color((r, g, b, 1.0))
            except ValueError: pass

    def swatch_pressed(self, instance):
        if instance.background_color != (0.2, 0.2, 0.2, 1): self.set_color(instance.background_color)

    def update_recent_colors(self, color):
        rgb_color = tuple(round(c, 2) for c in color[:3]) + (1.0,)
        if rgb_color in self.recent_colors: self.recent_colors.remove(rgb_color)
        self.recent_colors.insert(0, rgb_color)
        self.recent_colors = self.recent_colors[:256]
        if self.ids.palette_spinner.text == 'Recent': self.load_palette('Recent')

    def open_canvas_size_dialog(self):
        popup = DialogFactory.build_canvas_size_dialog(self.ids.canvas_widget.grid_size, self.ids.canvas_widget.change_grid_size)
        popup.open()

    def open_save_dialog(self):
        content = BoxLayout(orientation='vertical')
        file_chooser = FileChooserListView(path=os.getcwd(), filters=['*.json'])
        txt_input = TextInput(text='project.json', multiline=False, size_hint_y=0.1)
        btn_box = BoxLayout(size_hint_y=0.15)
        save_btn = Button(text='Save')
        cancel_btn = Button(text='Cancel')
        btn_box.add_widget(save_btn)
        btn_box.add_widget(cancel_btn)
        content.add_widget(file_chooser)
        content.add_widget(txt_input)
        content.add_widget(btn_box)
        popup = DialogFactory.create_popup('Save Project', content)
        def do_save(instance):
            filepath = os.path.join(file_chooser.path, txt_input.text)
            if not filepath.endswith('.json'): filepath += '.json'
            self.save_project(filepath)
            popup.dismiss()
        save_btn.bind(on_press=do_save)
        cancel_btn.bind(on_press=popup.dismiss)
        popup.open()

    def open_load_dialog(self):
        content = BoxLayout(orientation='vertical')
        file_chooser = FileChooserListView(path=os.getcwd(), filters=['*.json'])
        btn_box = BoxLayout(size_hint_y=0.15)
        load_btn = Button(text='Load')
        cancel_btn = Button(text='Cancel')
        btn_box.add_widget(load_btn)
        btn_box.add_widget(cancel_btn)
        content.add_widget(file_chooser)
        content.add_widget(btn_box)
        popup = DialogFactory.create_popup('Load Project', content)
        def do_load(instance):
            if file_chooser.selection: self.load_project(file_chooser.selection[0])
            popup.dismiss()
        load_btn.bind(on_press=do_load)
        cancel_btn.bind(on_press=popup.dismiss)
        popup.open()

    def open_import_dialog(self):
        if not PIL_AVAILABLE:
            show_error_popup("Dependency Missing", "Pillow library is not installed.\nPlease run: pip install Pillow")
            return
        content = BoxLayout(orientation='vertical')
        file_chooser = FileChooserListView(path=os.getcwd(), filters=['*.png', '*.jpg', '*.jpeg', '*.bmp'])
        btn_box = BoxLayout(size_hint_y=0.15)
        load_btn = Button(text='Import')
        cancel_btn = Button(text='Cancel')
        btn_box.add_widget(load_btn)
        btn_box.add_widget(cancel_btn)
        content.add_widget(file_chooser)
        content.add_widget(btn_box)
        popup = DialogFactory.create_popup('Import Image', content)
        def do_import(instance):
            if file_chooser.selection: self.import_image(file_chooser.selection[0])
            popup.dismiss()
        load_btn.bind(on_press=do_import)
        cancel_btn.bind(on_press=popup.dismiss)
        popup.open()

    def import_image(self, filepath):
        try:
            img = PILImage.open(filepath).convert('RGBA')
            cw = self.ids.canvas_widget
            img = img.resize((cw.grid_size, cw.grid_size), PILImage.NEAREST)
            
            new_layer = Layer(f"Imported {os.path.basename(filepath)}", cw.grid_size)
            for y in range(cw.grid_size):
                for x in range(cw.grid_size):
                    r, g, b, a = img.getpixel((x, cw.grid_size - 1 - y))
                    new_layer.pixels[y][x] = (r/255.0, g/255.0, b/255.0, a/255.0)
            new_layer.is_dirty = True
                    
            parent, idx = cw._find_parent(cw.active_frame.layers, cw.active_layer)
            if parent is not None: parent.insert(idx + 1, new_layer)
            else: cw.active_frame.layers.append(new_layer)
            
            cw.project.active_layer = new_layer
            cw.project.save_history()
            self.update_layer_ui()
            cw.recalculate_composite()
            cw.redraw_pixels()
            show_error_popup("Success", f"Imported {filepath} as a new layer.")
        except Exception as e:
            show_error_popup("Import Error", f"Could not import image:\n{e}")

    def save_project(self, filepath):
        cw = self.ids.canvas_widget
        data = {
            "grid_size": cw.grid_size,
            "active_frame_index": cw.project.active_frame_index,
            "is_tilemap_mode": cw.is_tilemap_mode,
            "tile_size": cw.tile_size,
            "frames": []
        }
        for frame in cw.project.frames:
            frame_data = {"layers": [self._layer_to_dict(l) for l in frame.layers]}
            data["frames"].append(frame_data)
        tmp = filepath + '.tmp'
        try:
            with open(tmp, 'w') as f: json.dump(data, f)
            os.replace(tmp, filepath)
        except OSError as e:
            show_error_popup("Save Error", f"Could not save project file:\n{e}")
            if os.path.exists(tmp): os.remove(tmp)

    def load_project(self, filepath):
        try:
            with open(filepath, 'r') as f: data = json.load(f)
        except Exception as e:
            show_error_popup("Load Error", f"Could not load project file:\n{e}")
            return
        cw = self.ids.canvas_widget
        new_grid_size = data.get("grid_size", 32)
        if new_grid_size != cw.grid_size: cw.change_grid_size(new_grid_size, keep_art=False)

        cw.project.frames = []
        for frame_data in data.get("frames", []):
            frame = Frame(cw.grid_size)
            frame.layers = [self._dict_to_layer(l, cw.grid_size) for l in frame_data.get("layers", [])]
            cw.project.frames.append(frame)
        if not cw.project.frames: cw.project.frames.append(Frame(cw.grid_size))
            
        cw.project.active_frame_index = min(data.get("active_frame_index", 0), len(cw.project.frames) - 1)
        cw.project.active_layer = cw.active_frame.layers[0]
        cw.is_tilemap_mode = data.get("is_tilemap_mode", False)
        cw.tile_size = data.get("tile_size", 16)
        
        if cw.is_tilemap_mode: self.ids.tilemap_mode_btn.state = 'down'
        else: self.ids.tilemap_mode_btn.state = 'normal'
        self.ids.tile_size_spinner.text = f"{cw.tile_size}px"
        
        cw.project.save_history()
        self.update_layer_ui()
        self.update_frame_ui()
        self.update_frame_thumbnails()
        cw.recalculate_composite()
        cw.redraw_pixels()

    def _layer_to_dict(self, layer):
        d = {
            "name": layer.name, "is_folder": layer.is_folder, "visible": layer.visible,
            "alpha_locked": layer.alpha_locked, "blend_mode": layer.blend_mode, "opacity": layer.opacity
        }
        if layer.is_folder: d["children"] = [self._layer_to_dict(c) for c in layer.children]
        else: d["pixels"] = [[list(px) for px in row] for row in layer.pixels]
        return d

    def _dict_to_layer(self, d, grid_size):
        try:
            layer = Layer(d.get("name", "Unnamed"), grid_size, d.get("is_folder", False))
            layer.visible = d.get("visible", True)
            layer.alpha_locked = d.get("alpha_locked", False)
            layer.blend_mode = d.get("blend_mode", "Normal")
            layer.opacity = d.get("opacity", 1.0)
            if layer.is_folder:
                for child_d in d.get("children", []): layer.children.append(self._dict_to_layer(child_d, grid_size))
            else:
                loaded_pixels = d.get("pixels", [])
                if len(loaded_pixels) == grid_size and all(len(r) == grid_size for r in loaded_pixels):
                    layer.pixels = [[tuple(px) for px in row] for row in loaded_pixels]
                else: layer.pixels = [[(0, 0, 0, 0) for _ in range(grid_size)] for _ in range(grid_size)]
            return layer
        except Exception as e: return Layer("Error Layer", grid_size, False)

    def open_adjustments_dialog(self):
        layout = BoxLayout(orientation='vertical', padding=10, spacing=10)
        h_slider = Slider(min=-1.0, max=1.0, value=0, step=0.05)
        s_slider = Slider(min=-1.0, max=1.0, value=0, step=0.05)
        v_slider = Slider(min=-1.0, max=1.0, value=0, step=0.05)
        layout.add_widget(Label(text='Hue Shift', color=(1,1,1,1)))
        layout.add_widget(h_slider)
        layout.add_widget(Label(text='Saturation Shift', color=(1,1,1,1)))
        layout.add_widget(s_slider)
        layout.add_widget(Label(text='Value Shift', color=(1,1,1,1)))
        layout.add_widget(v_slider)
        btn = Button(text='Apply', size_hint=(1, 0.2), background_color=(0.2, 0.8, 0.2, 1))
        layout.add_widget(btn)
        popup = DialogFactory.create_popup('Adjustments', layout, (0.5, 0.6))
        def do_apply(instance):
            self.ids.canvas_widget.apply_adjustments(h_slider.value, s_slider.value, v_slider.value)
            popup.dismiss()
        btn.bind(on_press=do_apply)
        popup.open()

    def open_new_canvas_dialog(self):
        layout = BoxLayout(orientation='vertical', padding=10, spacing=10)
        controls = BoxLayout(orientation='horizontal', size_hint_y=0.4, spacing=5)
        controls.add_widget(Label(text='Size:', color=(1,1,1,1), size_hint_x=0.6))
        size_input = TextInput(text='32', multiline=False, input_filter='int')
        controls.add_widget(size_input)
        layout.add_widget(controls)
        
        btn_box = BoxLayout(orientation='horizontal', size_hint_y=0.4, spacing=5)
        apply_btn = Button(text='Create', background_color=(0.2, 0.8, 0.2, 1))
        cancel_btn = Button(text='Cancel', background_color=(0.8, 0.2, 0.2, 1))
        btn_box.add_widget(apply_btn)
        btn_box.add_widget(cancel_btn)
        layout.add_widget(btn_box)
        popup = DialogFactory.create_popup('New Canvas', layout, (0.5, 0.4))
        def do_apply(instance):
            try:
                new_size = int(size_input.text)
                if new_size > 0:
                    cw = self.ids.canvas_widget
                    cw.project.frames = [Frame(new_size)]
                    cw.project.grid_size = new_size
                    cw.grid_size = new_size
                    cw.change_grid_size(new_size, keep_art=False)
                    cw.project.save_history()
                    self.update_layer_ui()
                    self.update_frame_ui()
            except ValueError: pass
            popup.dismiss()
        apply_btn.bind(on_press=do_apply)
        cancel_btn.bind(on_press=popup.dismiss)
        popup.open()

    def open_color_slider_dialog(self, mode='rgb'):
        layout = BoxLayout(orientation='vertical', padding=10, spacing=10)
        
        r_slider = Slider(min=0.0, max=1.0, value=self.ids.color_wheel.color[0])
        g_slider = Slider(min=0.0, max=1.0, value=self.ids.color_wheel.color[1])
        b_slider = Slider(min=0.0, max=1.0, value=self.ids.color_wheel.color[2])
        
        def update_color(instance, val):
            self.set_color((r_slider.value, g_slider.value, b_slider.value, 1.0))
            
        r_slider.bind(on_touch_move=update_color)
        g_slider.bind(on_touch_move=update_color)
        b_slider.bind(on_touch_move=update_color)
        
        layout.add_widget(Label(text='Red', color=(1,1,1,1)))
        layout.add_widget(r_slider)
        layout.add_widget(Label(text='Green', color=(1,1,1,1)))
        layout.add_widget(g_slider)
        layout.add_widget(Label(text='Blue', color=(1,1,1,1)))
        layout.add_widget(b_slider)
        
        if mode == 'hsv':
            h_slider = Slider(min=0.0, max=1.0, value=0.0)
            s_slider = Slider(min=0.0, max=1.0, value=1.0)
            v_slider = Slider(min=0.0, max=1.0, value=1.0)
            def update_color_hsv(instance, val):
                r, g, b = colorsys.hsv_to_rgb(h_slider.value, s_slider.value, v_slider.value)
                self.set_color((r, g, b, 1.0))
            h_slider.bind(on_touch_move=update_color_hsv)
            s_slider.bind(on_touch_move=update_color_hsv)
            v_slider.bind(on_touch_move=update_color_hsv)
            layout.add_widget(Label(text='Hue', color=(1,1,1,1)))
            layout.add_widget(h_slider)
            layout.add_widget(Label(text='Saturation', color=(1,1,1,1)))
            layout.add_widget(s_slider)
            layout.add_widget(Label(text='Value', color=(1,1,1,1)))
            layout.add_widget(v_slider)
        
        btn = Button(text='Close', size_hint=(1, 0.2), background_color=(0.8, 0.2, 0.2, 1))
        layout.add_widget(btn)
        popup = DialogFactory.create_popup(f'{mode.upper()} Sliders', layout, (0.5, 0.8))
        btn.bind(on_press=popup.dismiss)
        popup.open()

    def open_brush_creator(self):
        layout = BoxLayout(orientation='vertical', padding=10, spacing=10)
        name_input = TextInput(text='My Brush', multiline=False, size_hint_y=0.1)
        shape_spinner = Spinner(text='soft_circle', values=['square', 'circle', 'soft_circle', 'scatter', 'noise', 'dither', 'hatch', 'hatch_cross'], size_hint_y=0.1)
        hard_slider = Slider(min=0.0, max=1.0, value=0.5)
        jitter_slider = Slider(min=0.0, max=1.0, value=0.0)
        space_slider = Slider(min=0.01, max=0.5, value=0.1)
        opa_slider = Slider(min=0.1, max=1.0, value=1.0)
        layout.add_widget(Label(text='Name:', color=(1,1,1,1), size_hint_y=0.05))
        layout.add_widget(name_input)
        layout.add_widget(Label(text='Shape:', color=(1,1,1,1), size_hint_y=0.05))
        layout.add_widget(shape_spinner)
        for txt, sld in [('Hardness', hard_slider), ('Jitter', jitter_slider), ('Spacing', space_slider), ('Opacity', opa_slider)]:
            layout.add_widget(Label(text=txt, color=(1,1,1,1), size_hint_y=0.05))
            layout.add_widget(sld)
        btn = Button(text='Save Brush', size_hint_y=0.15, background_color=(0.2, 0.8, 0.2, 1))
        layout.add_widget(btn)
        popup = DialogFactory.create_popup('Brush Creator', layout, (0.5, 0.8))
        def save_brush(instance):
            new_brush = {
                "name": name_input.text, "shape": shape_spinner.text,
                "hardness": hard_slider.value, "jitter": jitter_slider.value,
                "spacing": space_slider.value, "size_jitter": 0.0,
                "blend": True, "opacity_mult": opa_slider.value
            }
            try:
                filepath = 'brushes/custom_brushes.json'
                with open(filepath, 'r+') as f:
                    data = json.load(f)
                    data['brushes'].append(new_brush)
                    f.seek(0)
                    json.dump(data, f, indent=4)
                    f.truncate()
                self.reload_brushes()
                popup.dismiss()
            except Exception as e: show_error_popup("Error", str(e))
        btn.bind(on_press=save_brush)
        popup.open()

    def open_palette_creator(self):
        layout = BoxLayout(orientation='vertical', padding=10, spacing=10)
        name_input = TextInput(text='My Palette', multiline=False, size_hint_y=0.1)
        layout.add_widget(name_input)
        grid = GridLayout(cols=4, rows=4, spacing=2)
        color_btns = []
        for i in range(16):
            btn = Button(background_color=(0,0,0,1))
            btn.bind(on_press=lambda inst, *args: setattr(inst, 'background_color', self.ids.color_wheel.color))
            color_btns.append(btn)
            grid.add_widget(btn)
        layout.add_widget(grid)
        btn = Button(text='Save Palette', size_hint_y=0.15, background_color=(0.2, 0.8, 0.2, 1))
        layout.add_widget(btn)
        popup = DialogFactory.create_popup('Palette Creator', layout, (0.4, 0.6))
        def save_pal(instance):
            colors = [btn.background_color for btn in color_btns]
            try:
                filepath = 'palettes/custom_palettes.json'
                with open(filepath, 'r+') as f:
                    data = json.load(f)
                    data['palettes'][name_input.text] = colors
                    f.seek(0)
                    json.dump(data, f, indent=4)
                    f.truncate()
                load_custom_palettes()
                self.update_palette_spinner()
                popup.dismiss()
            except Exception as e: show_error_popup("Error", str(e))
        btn.bind(on_press=save_pal)
        popup.open()

    def update_brush_size(self, value):
        self.ids.canvas_widget.brush_size = int(value)
        self.ids.size_label.text = f"Size: {int(value)}"

    def update_opacity(self, value):
        self.ids.canvas_widget.brush_opacity = value
        self.ids.opacity_label.text = f"Opacity: {int(value * 100)}%"

    def update_tolerance(self, value):
        self.ids.canvas_widget.fill_tolerance = int(value)
        self.ids.tolerance_label.text = f"Tol: {int(value)}"

    def update_layer_opacity(self, value):
        self.ids.canvas_widget.active_layer.opacity = value
        self.ids.canvas_widget.recalculate_composite()
        self.ids.canvas_widget.redraw_pixels()

    def set_brush_type(self, text):
        self.ids.canvas_widget.brush_type = text

# ==========================================
# 10. APP ENTRY POINT (with Splash Screen)
# ==========================================
class PixelArtApp(App):
    def build(self):
        self.load_box = BoxLayout(orientation='vertical', padding=50, spacing=20)
        with self.load_box.canvas.before:
            Color(0.12, 0.12, 0.15, 1)
            self.load_bg_rect = Rectangle(pos=self.load_box.pos, size=self.load_box.size)
        self.load_box.bind(size=self._update_load_rect, pos=self._update_load_rect)
        
        self.load_label = Label(text='Initializing Engine...', font_size=24, color=(1,1,1,1))
        self.load_bar = ProgressBar(max=10, value=1)
        self.load_box.add_widget(self.load_label)
        self.load_box.add_widget(self.load_bar)
        
        Clock.schedule_once(self._actual_build, 0.1)
        return self.load_box

    def _update_load_rect(self, instance, value):
        self.load_bg_rect.pos = instance.pos
        self.load_bg_rect.size = instance.size

    def _actual_build(self, dt):
        self.load_bar.value = 3
        self.load_label.text = 'Loading Layout...'
        Builder.load_string(KV_LAYOUT)
        
        self.load_bar.value = 6
        self.load_label.text = 'Initializing Tools...'
        root = RootWidget()
        
        def on_color_change(instance, color):
            root.ids.canvas_widget.current_color = color
            root.update_recent_colors(color)
            
        event_bus.bind(on_color_change=on_color_change)
        root.ids.canvas_widget.current_color = root.ids.color_wheel.color
        
        r, g, b = int(root.ids.color_wheel.color[0]*255), int(root.ids.color_wheel.color[1]*255), int(root.ids.color_wheel.color[2]*255)
        root.ids.hex_input.text = f"{r:02X}{g:02X}{b:02X}"
        
        self.load_bar.value = 8
        self.load_label.text = 'Binding Events...'
        root.ids.color_wheel.bind(color=lambda inst, val: event_bus.broadcast_color(val))
        root.ids.canvas_widget.recalculate_composite()
        root.ids.canvas_widget.redraw_pixels()
        
        Window.bind(on_key_down=self.on_key_down)
        Window.bind(on_key_up=self.on_key_up)
        
        self.load_bar.value = 10
        self.load_label.text = 'Ready!'
        
        self.root.clear_widgets()
        self.root.add_widget(root)

    def on_key_down(self, instance, keyboard, keycode, text, modifiers):
        root = self.root.children[0] if self.root.children else None
        if not isinstance(root, RootWidget): return
        cw = root.ids.canvas_widget
        
        from kivy.uix.textinput import TextInput
        if isinstance(root.get_focus_widget(), TextInput): return
            
        if keyboard == 32: cw.is_space_pressed = True
        if 'shift' in modifiers: cw.is_shift_pressed = True
        if 'alt' in modifiers: cw.is_alt_pressed = True
            
        c = text.lower() if text else ''
        
        if 'ctrl' in modifiers:
            if c == 'z': cw.undo()
            elif c == 'y': cw.redo()
            elif c == 's': cw.save_png()
            elif c == 'd': cw.clear_selection()
            elif c == 'a': cw.select_all()
            elif c == 'c': cw.copy_selection()
            elif c == 'x': cw.cut_selection()
            elif c == 'v': cw.paste_selection()
            elif c == 'j': cw.duplicate_selection()
            if 'shift' in modifiers:
                if c == 'h': cw.flip_selection_h()
                elif c == 'v': cw.flip_selection_v()
                
        if not modifiers or (len(modifiers) == 1 and modifiers[0] == 'shift'):
            if keyboard == 273: cw.shift_pixels(0, 1)   # Up
            elif keyboard == 274: cw.shift_pixels(0, -1) # Down
            elif keyboard == 275: cw.shift_pixels(1, 0)  # Right
            elif keyboard == 276: cw.shift_pixels(-1, 0) # Left
            
            elif c == 'b': root.set_tool('brush')
            elif c == 'l': root.set_tool('line')
            elif c == 'r': root.set_tool('rect')
            elif c == 'o': root.set_tool('ellipse')
            elif c == 'u': root.set_tool('gradient')
            elif c == 's': root.set_tool('select')
            elif c == 'w': root.set_tool('magic_wand')
            elif c == 'g': root.set_tool('fill')
            elif c == 'i': root.set_tool('picker')
            elif c == 'e': root.set_tool('eraser')
            elif c == 'm': root.set_tool('move')
            elif c == 'p': root.toggle_playback()
            
            elif c == '[': root.update_brush_size(max(1, int(root.ids.size_slider.value) - 1))
            elif c == ']': root.update_brush_size(min(15, int(root.ids.size_slider.value) + 1))

    def on_key_up(self, instance, keyboard, keycode, text, modifiers):
        root = self.root.children[0] if self.root.children else None
        if not isinstance(root, RootWidget): return
        cw = root.ids.canvas_widget
        if keyboard == 32: cw.is_space_pressed = False
        if 'shift' not in modifiers:
            cw.is_shift_pressed = False
            cw.shift_line_start = None 
        if 'alt' not in modifiers: cw.is_alt_pressed = False

if __name__ == '__main__':
    PixelArtApp().run()