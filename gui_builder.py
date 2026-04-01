import tkinter as tk
from tkinter import ttk, messagebox, filedialog, colorchooser
import json
import os
import copy

# --- Иконки (символы Unicode для простоты) ---
ICONS = {
    "Label": "🏷️", "Button": "🔘", "Entry": "📝", "Checkbutton": "☑️",
    "Radiobutton": "🔘", "Listbox": "📋", "Text": "📄", "Scale": "🎚️",
    "Canvas": "🎨", "Frame": "🖼️", "Notebook": "📑", "PanedWindow": "⚖️"
}

class UndoManager:
    """Менеджер истории действий (Undo/Redo)"""
    def __init__(self, app):
        self.app = app
        self.undo_stack = []
        self.redo_stack = []
        self.max_steps = 50

    def save_state(self, action_name=""):
        state = copy.deepcopy([{"type": w.widget_type, "x": w.x, "y": w.y, "config": w.config.copy()} for w in self.app.widgets])
        if len(self.undo_stack) >= self.max_steps:
            self.undo_stack.pop(0)
        self.undo_stack.append((action_name, state))
        self.redo_stack.clear()
        self.app.update_status(f"Действие: {action_name}")

    def undo(self):
        if not self.undo_stack:
            return
        action_name, state = self.undo_stack.pop()
        current_state = [{"type": w.widget_type, "x": w.x, "y": w.y, "config": w.config.copy()} for w in self.app.widgets]
        self.redo_stack.append((action_name, current_state))
        self.app.restore_state(state)
        self.app.update_status(f"Отменено: {action_name}")

    def redo(self):
        if not self.redo_stack:
            return
        action_name, state = self.redo_stack.pop()
        current_state = [{"type": w.widget_type, "x": w.x, "y": w.y, "config": w.config.copy()} for w in self.app.widgets]
        self.undo_stack.append((action_name, current_state))
        self.app.restore_state(state)
        self.app.update_status(f"Повторено: {action_name}")

class WidgetItem:
    def __init__(self, widget_type, x, y, config, parent_id=None):
        self.widget_type = widget_type
        self.x = x
        self.y = y
        self.config = config
        self.parent_id = parent_id  # Для вложенности (Notebook, Frame)
        self.widget_instance = None
        self.id = id(self)
        self.events = {}  # Хранение привязок событий

class GUIBuilderApp:
    def __init__(self, root):
        self.root = root
        self.root.title("🚀 Ultimate Tkinter Constructor AI")
        self.root.geometry("1400x900")

        # Настройки стиля
        style = ttk.Style()
        style.theme_use('clam')

        # Данные проекта
        self.widgets = []
        self.selected_widgets = []  # Поддержка множественного выделения
        self.drag_data = {"items": [], "start_x": 0, "start_y": 0}
        self.clipboard = None
        self.current_mode = "move"
        self.current_widget_type = None
        self.snap_to_grid = True
        self.grid_size = 10

        # Менеджер отмены
        self.undo_manager = UndoManager(self)

        self.setup_ui()
        self.bind_events()
        self.load_templates()

    def setup_ui(self):
        # --- Верхняя панель ---
        top_frame = ttk.Frame(self.root)
        top_frame.pack(fill=tk.X, padx=10, pady=5)

        ttk.Button(top_frame, text="💾 Сохранить", command=self.save_project).pack(side=tk.LEFT, padx=2)
        ttk.Button(top_frame, text="📂 Открыть", command=self.load_project).pack(side=tk.LEFT, padx=2)
        ttk.Button(top_frame, text="🐍 Код", command=self.generate_code).pack(side=tk.LEFT, padx=2)
        ttk.Button(top_frame, text="▶️ Предпросмотр", command=self.preview).pack(side=tk.LEFT, padx=2)
        ttk.Button(top_frame, text="↩️ Отмена", command=lambda: self.undo_manager.undo()).pack(side=tk.LEFT, padx=10)
        ttk.Button(top_frame, text="↪️ Повтор", command=lambda: self.undo_manager.redo()).pack(side=tk.LEFT, padx=2)

        ttk.Checkbutton(top_frame, text="Сетка", variable=tk.BooleanVar(value=True), command=self.toggle_grid).pack(side=tk.RIGHT, padx=5)

        self.status_label = ttk.Label(top_frame, text="Готов", foreground="gray")
        self.status_label.pack(side=tk.RIGHT, padx=10)

        # --- Основная область ---
        main_paned = ttk.PanedWindow(self.root, orient=tk.HORIZONTAL)
        main_paned.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)

        # 1. Панель инструментов (Слева)
        tool_frame = ttk.LabelFrame(main_paned, text="🧰 Виджеты", padding=10)
        main_paned.add(tool_frame, weight=1)

        # Поиск виджетов
        search_entry = ttk.Entry(tool_frame)
        search_entry.pack(fill=tk.X, pady=(0, 5))
        search_entry.bind("<KeyRelease>", lambda e: self.filter_widgets(search_entry.get()))

        self.widget_buttons = {}
        widget_types = [
            ("Label", "Текст"), ("Button", "Кнопка"), ("Entry", "Ввод"),
            ("Checkbutton", "Чекбокс"), ("Radiobutton", "Радио"), ("Listbox", "Список"),
            ("Text", "Текст"), ("Scale", "Ползунок"), ("Canvas", "Холст"),
            ("Frame", "Фрейм"), ("Notebook", "Вкладки"), ("PanedWindow", "Панель")
        ]

        for w_type, w_name in widget_types:
            btn = ttk.Button(tool_frame, text=f"{ICONS.get(w_type, '')} {w_name}",
                           command=lambda t=w_type: self.set_add_mode(t))
            btn.pack(fill=tk.X, pady=2, ipady=3)
            self.widget_buttons[w_type] = btn

        # Библиотека шаблонов
        ttk.Separator(tool_frame, orient='horizontal').pack(fill=tk.X, pady=10)
        ttk.Label(tool_frame, text="📦 Шаблоны", font=("Arial", 10, "bold")).pack(anchor=tk.W)

        self.template_listbox = tk.Listbox(tool_frame, height=5)
        self.template_listbox.pack(fill=tk.X, pady=2)
        self.template_listbox.bind("<Double-Button-1>", self.insert_template)

        # AI Помощник
        ttk.Separator(tool_frame, orient='horizontal').pack(fill=tk.X, pady=10)
        ttk.Label(tool_frame, text="🤖 AI Генератор", font=("Arial", 10, "bold")).pack(anchor=tk.W)
        self.ai_entry = ttk.Entry(tool_frame)
        self.ai_entry.pack(fill=tk.X, pady=2)
        self.ai_entry.insert(0, "Форма входа...")
        ttk.Button(tool_frame, text="Сгенерировать", command=self.ai_generate).pack(fill=tk.X, pady=2)

        # 2. Холст (Центр)
        canvas_container = ttk.LabelFrame(main_paned, text="🎨 Рабочая область", padding=5)
        main_paned.add(canvas_container, weight=4)

        # Линейки
        ruler_h = tk.Canvas(canvas_container, height=20, bg="#f0f0f0", highlightthickness=0)
        ruler_h.pack(fill=tk.X)
        self.ruler_h = ruler_h

        canvas_frame = tk.Frame(canvas_container)
        canvas_frame.pack(fill=tk.BOTH, expand=True)

        self.canvas = tk.Canvas(canvas_frame, bg="white", highlightthickness=0)
        self.canvas.pack(fill=tk.BOTH, expand=True)

        ruler_v = tk.Canvas(canvas_container, width=20, bg="#f0f0f0", highlightthickness=0)
        ruler_v.pack(side=tk.RIGHT, fill=tk.Y)
        self.ruler_v = ruler_v

        # Сетка
        self.draw_grid()

        # События
        self.canvas.bind("<ButtonPress-1>", self.on_canvas_press)
        self.canvas.bind("<B1-Motion>", self.on_canvas_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_canvas_release)
        self.canvas.bind("<Double-Button-1>", self.on_canvas_double_click)
        self.canvas.bind("<Button-3>", self.show_context_menu)

        self.mode_label = ttk.Label(canvas_container, text="Режим: Перемещение", foreground="blue")
        self.mode_label.pack(anchor=tk.W)

        # 3. Панель свойств и Дерево (Справа)
        right_paned = ttk.PanedWindow(main_paned, orient=tk.VERTICAL)
        main_paned.add(right_paned, weight=1)

        # Дерево виджетов
        tree_frame = ttk.LabelFrame(right_paned, text="🌳 Структура", padding=5)
        right_paned.add(tree_frame, weight=0)  # Убрал height, добавил weight=0 чтобы не растягивался сильно

        self.widget_tree = ttk.Treeview(tree_frame, columns=("Type", "Name"), height=6)
        self.widget_tree.heading("#0", text="ID")
        self.widget_tree.heading("Type", text="Тип")
        self.widget_tree.heading("Name", text="Имя")
        self.widget_tree.pack(fill=tk.BOTH, expand=True)
        self.widget_tree.bind("<<TreeviewSelect>>", self.on_tree_select)

        # Свойства
        prop_frame = ttk.LabelFrame(right_paned, text="⚙️ Свойства", padding=10)
        right_paned.add(prop_frame, weight=1)

        # Вкладки свойств
        prop_notebook = ttk.Notebook(prop_frame)
        prop_notebook.pack(fill=tk.BOTH, expand=True)

        # Основные свойства
        basic_frame = ttk.Frame(prop_notebook)
        prop_notebook.add(basic_frame, text="Основные")

        self.prop_widgets = {}
        common_props = ["text", "bg", "fg", "width", "height", "font", "command"]

        row = 0
        for prop in common_props:
            ttk.Label(basic_frame, text=f"{prop}:").grid(row=row, column=0, sticky=tk.W, pady=3)
            entry = ttk.Entry(basic_frame)
            entry.grid(row=row, column=1, sticky=tk.EW, pady=3, padx=(5,0))
            entry.bind("<KeyRelease>", lambda e, p=prop: self.update_property(p))
            self.prop_widgets[prop] = entry

            # Кнопка выбора цвета
            if prop in ["bg", "fg"]:
                btn = ttk.Button(basic_frame, text="🎨", width=2,
                               command=lambda p=prop: self.choose_color(p))
                btn.grid(row=row, column=2, padx=(2,0))
            row += 1

        # События
        events_frame = ttk.Frame(prop_notebook)
        prop_notebook.add(events_frame, text="События")

        self.event_widgets = {}
        event_types = ["<Button-1>", "<Double-Button-1>", "<Enter>", "<Leave>", "<Key>"]

        for i, evt in enumerate(event_types):
            ttk.Label(events_frame, text=evt).grid(row=i, column=0, sticky=tk.W, pady=3)
            entry = ttk.Entry(events_frame)
            entry.grid(row=i, column=1, sticky=tk.EW, pady=3, padx=(5,0))
            self.event_widgets[evt] = entry
            row += 1

        ttk.Button(prop_frame, text="🗑️ Удалить выбранное", command=self.delete_selected).pack(fill=tk.X, pady=10)

        # Контекстное меню
        self.context_menu = tk.Menu(self.root, tearoff=0)
        self.context_menu.add_command(label="✂️ Вырезать", command=self.cut_selection)
        self.context_menu.add_command(label="📋 Копировать", command=self.copy_selection)
        self.context_menu.add_command(label="📌 Вставить", command=self.paste_selection)
        self.context_menu.add_separator()
        self.context_menu.add_command(label="🗑️ Удалить", command=self.delete_selected)
        self.context_menu.add_command(label="📤 На передний план", command=self.bring_to_front)
        self.context_menu.add_command(label="📥 На задний план", command=self.send_to_back)

    def bind_events(self):
        # Глобальные горячие клавиши
        self.root.bind("<Control-z>", lambda e: self.undo_manager.undo())
        self.root.bind("<Control-y>", lambda e: self.undo_manager.redo())
        self.root.bind("<Control-c>", lambda e: self.copy_selection())
        self.root.bind("<Control-v>", lambda e: self.paste_selection())
        self.root.bind("<Control-x>", lambda e: self.cut_selection())
        self.root.bind("<Delete>", lambda e: self.delete_selected())

    def toggle_grid(self):
        self.snap_to_grid = not self.snap_to_grid
        if self.snap_to_grid:
            self.draw_grid()
        else:
            self.canvas.delete("grid")

    def draw_grid(self):
        self.canvas.delete("grid")
        if not self.snap_to_grid:
            return
        w, h = 2000, 2000
        for i in range(0, w, self.grid_size):
            self.canvas.create_line(i, 0, i, h, fill="#e0e0e0", tags="grid")
            self.canvas.create_line(0, i, w, i, fill="#e0e0e0", tags="grid")

    def update_rulers(self):
        # Обновление линеек при прокрутке (упрощенно)
        pass

    def set_add_mode(self, widget_type):
        self.current_mode = "add"
        self.current_widget_type = widget_type
        self.mode_label.config(text=f"Режим: Добавление {ICONS.get(widget_type, '')} {widget_type}")
        self.deselect_all()

    def on_canvas_press(self, event):
        if self.current_mode == "add":
            self.place_widget(event.x, event.y)
        else:
            # Выделение области или выбор виджета
            item = self.canvas.find_withtag("current")
            if item:
                tags = self.canvas.gettags(item[0])
                widget_id = None
                for tag in tags:
                    if tag.startswith("widget_"):
                        widget_id = tag.split("_")[1]
                        break
                if widget_id:
                    # Проверка на множественное выделение (Shift)
                    if event.state & 0x1:  # Shift pressed
                        if widget_id in self.selected_widgets:
                            self.selected_widgets.remove(widget_id)
                        else:
                            self.selected_widgets.append(widget_id)
                    else:
                        if widget_id not in self.selected_widgets:
                            self.deselect_all()
                            self.selected_widgets.append(widget_id)

                    self.select_widgets(self.selected_widgets)
                    self.drag_data["start_x"] = event.x
                    self.drag_data["start_y"] = event.y

    def on_canvas_drag(self, event):
        if self.selected_widgets and self.current_mode == "move":
            dx = event.x - self.drag_data["start_x"]
            dy = event.y - self.drag_data["start_y"]

            for wid in self.selected_widgets:
                widget_obj = next((w for w in self.widgets if str(w.id) == wid), None)
                if widget_obj and widget_obj.widget_instance:
                    new_x = widget_obj.x + dx
                    new_y = widget_obj.y + dy

                    if self.snap_to_grid:
                        new_x = round(new_x / self.grid_size) * self.grid_size
                        new_y = round(new_y / self.grid_size) * self.grid_size

                    self.canvas.move(widget_obj.widget_instance, dx, dy)
                    widget_obj.x = new_x
                    widget_obj.y = new_y

            self.drag_data["start_x"] = event.x
            self.drag_data["start_y"] = event.y
            self.update_rulers()

    def on_canvas_release(self, event):
        if self.drag_data["items"] or self.selected_widgets:
            self.undo_manager.save_state("Перемещение")
        self.drag_data["items"] = []
        if self.current_mode == "add":
            self.current_mode = "move"
            self.mode_label.config(text="Режим: Перемещение")

    def on_canvas_double_click(self, event):
        # Быстрое добавление последнего использованного виджета
        if self.current_widget_type:
            self.place_widget(event.x, event.y)

    def place_widget(self, x, y):
        if self.snap_to_grid:
            x = round(x / self.grid_size) * self.grid_size
            y = round(y / self.grid_size) * self.grid_size

        default_config = {
            "text": f"My {self.current_widget_type}",
            "bg": "#f0f0f0", "fg": "black", "width": 10, "height": 1
        }

        if self.current_widget_type == "Entry":
            default_config = {"text": "", "bg": "white", "fg": "black", "width": 20}
        elif self.current_widget_type == "Text":
            default_config = {"text": "", "bg": "white", "fg": "black", "width": 30, "height": 5}
        elif self.current_widget_type == "Notebook":
            default_config = {"width": 200, "height": 100}
            del default_config["text"]

        new_widget = WidgetItem(self.current_widget_type, x, y, default_config.copy())
        self.widgets.append(new_widget)
        self.render_widget(new_widget)
        self.update_tree()

        self.deselect_all()
        self.selected_widgets.append(str(new_widget.id))
        self.select_widgets(self.selected_widgets)

        self.undo_manager.save_state(f"Добавлен {self.current_widget_type}")

        self.current_mode = "move"
        self.mode_label.config(text="Режим: Перемещение")

    def render_widget(self, widget_obj):
        if widget_obj.widget_instance:
            self.canvas.delete(widget_obj.widget_instance)

        w_type = widget_obj.widget_type
        config = widget_obj.config

        try:
            frame = tk.Frame(self.canvas, bg="#ddd", relief=tk.RAISED, bd=1)

            if w_type == "Label":
                w = tk.Label(frame, text=config.get("text", ""), bg=config.get("bg"), fg=config.get("fg"))
            elif w_type == "Button":
                w = tk.Button(frame, text=config.get("text", ""), bg=config.get("bg"), fg=config.get("fg"))
            elif w_type == "Entry":
                w = tk.Entry(frame, width=config.get("width", 20))
                w.insert(0, config.get("text", ""))
            elif w_type == "Checkbutton":
                w = tk.Checkbutton(frame, text=config.get("text", ""), bg=config.get("bg"))
            elif w_type == "Radiobutton":
                w = tk.Radiobutton(frame, text=config.get("text", ""), bg=config.get("bg"))
            elif w_type == "Listbox":
                w = tk.Listbox(frame, height=config.get("height", 5))
            elif w_type == "Text":
                w = tk.Text(frame, width=config.get("width", 30), height=config.get("height", 5))
            elif w_type == "Scale":
                w = tk.Scale(frame, orient=tk.HORIZONTAL)
            elif w_type == "Canvas":
                w = tk.Canvas(frame, width=config.get("width", 100), height=config.get("height", 50), bg=config.get("bg", "white"))
            elif w_type == "Frame":
                w = tk.Frame(frame, width=config.get("width", 50), height=config.get("height", 50), bg=config.get("bg"))
                w.propagate(False)
            elif w_type == "Notebook":
                w = ttk.Notebook(frame, width=config.get("width", 200), height=config.get("height", 100))
                w.propagate(False)
            else:
                w = tk.Label(frame, text="Unknown")

            w.pack(fill=tk.BOTH, expand=True)

            # Привязка событий
            frame.bind("<Button-1>", lambda e, obj=widget_obj: self.on_widget_click(obj))
            w.bind("<Button-1>", lambda e, obj=widget_obj: self.on_widget_click(obj))

            widget_id = self.canvas.create_window(widget_obj.x, widget_obj.y, window=frame, anchor="nw",
                                                tags=f"widget_{widget_obj.id}")
            widget_obj.widget_instance = widget_id

        except Exception as e:
            print(f"Error rendering {w_type}: {e}")

    def on_widget_click(self, widget_obj):
        if self.current_mode != "add":
            self.deselect_all()
            self.selected_widgets.append(str(widget_obj.id))
            self.select_widgets(self.selected_widgets)

    def select_widgets(self, widget_ids):
        self.deselect_all()
        self.selected_widgets = list(widget_ids)

        for wid in widget_ids:
            widget_obj = next((w for w in self.widgets if str(w.id) == wid), None)
            if widget_obj:
                # Рисуем рамку выделения НА CANVAS, а не меняем виджет
                x, y = widget_obj.x, widget_obj.y
                w, h = widget_obj.width, widget_obj.height
                rect = self.canvas.create_rectangle(
                    x - 2, y - 2, x + w + 2, y + h + 2,
                    outline="blue", width=2, tags=("selection", f"sel_{wid}")
                )
                widget_obj.selection_rect = rect

        if widget_ids:
            widget_obj = next((w for w in self.widgets if str(w.id) == widget_ids[0]), None)
            if widget_obj:
                self.prop_widgets["text"].delete(0, tk.END)
                self.prop_widgets["text"].insert(0, widget_obj.config.get("text", ""))
                self.prop_widgets["bg"].delete(0, tk.END)
                self.prop_widgets["bg"].insert(0, widget_obj.config.get("bg", ""))
                self.prop_widgets["fg"].delete(0, tk.END)
                self.prop_widgets["fg"].insert(0, widget_obj.config.get("fg", ""))

                # Загрузка событий
                for evt, entry in self.event_widgets.items():
                    entry.delete(0, tk.END)
                    entry.insert(0, widget_obj.events.get(evt, ""))

    def deselect_all(self):
        # Удаляем все прямоугольники выделения с canvas
        self.canvas.delete("selection")
        for wid in self.selected_widgets:
            widget_obj = next((w for w in self.widgets if str(w.id) == wid), None)
            if widget_obj:
                widget_obj.selection_rect = None
        self.selected_widgets = []

    def update_property(self, prop_name):
        if not self.selected_widgets:
            return

        value = self.prop_widgets[prop_name].get()

        for wid in self.selected_widgets:
            widget_obj = next((w for w in self.widgets if str(w.id) == wid), None)
            if widget_obj:
                if prop_name in ["width", "height"]:
                    try: value = int(value)
                    except: pass
                widget_obj.config[prop_name] = value

        for wid in self.selected_widgets:
            widget_obj = next((w for w in self.widgets if str(w.id) == wid), None)
            if widget_obj:
                self.render_widget(widget_obj)

        self.undo_manager.save_state(f"Изменено {prop_name}")

    def choose_color(self, prop_name):
        color = colorchooser.askcolor()[1]
        if color:
            self.prop_widgets[prop_name].delete(0, tk.END)
            self.prop_widgets[prop_name].insert(0, color)
            self.update_property(prop_name)

    def delete_selected(self):
        if not self.selected_widgets:
            return

        for wid in self.selected_widgets[:]:
            widget_obj = next((w for w in self.widgets if str(w.id) == wid), None)
            if widget_obj:
                if widget_obj.widget_instance:
                    self.canvas.delete(widget_obj.widget_instance)
                self.widgets.remove(widget_obj)

        self.deselect_all()
        self.update_tree()
        self.undo_manager.save_state("Удаление")

    def cut_selection(self):
        self.copy_selection()
        self.delete_selected()

    def copy_selection(self):
        if not self.selected_widgets:
            return

        self.clipboard = []
        for wid in self.selected_widgets:
            widget_obj = next((w for w in self.widgets if str(w.id) == wid), None)
            if widget_obj:
                self.clipboard.append({
                    "type": widget_obj.widget_type,
                    "x": widget_obj.x,
                    "y": widget_obj.y,
                    "config": widget_obj.config.copy(),
                    "events": widget_obj.events.copy()
                })
        self.update_status(f"Скопировано {len(self.clipboard)} элементов")

    def paste_selection(self):
        if not self.clipboard:
            return

        self.deselect_all()
        for item in self.clipboard:
            new_widget = WidgetItem(item["type"], item["x"] + 20, item["y"] + 20, item["config"].copy())
            new_widget.events = item["events"].copy()
            self.widgets.append(new_widget)
            self.render_widget(new_widget)
            self.selected_widgets.append(str(new_widget.id))

        self.select_widgets(self.selected_widgets)
        self.update_tree()
        self.undo_manager.save_state("Вставка")

    def bring_to_front(self):
        # Сортировка виджетов
        pass

    def send_to_back(self):
        pass

    def show_context_menu(self, event):
        self.context_menu.post(event.x_root, event.y_root)

    def update_tree(self):
        for item in self.widget_tree.get_children():
            self.widget_tree.delete(item)

        for w in self.widgets:
            self.widget_tree.insert("", tk.END, iid=str(w.id), text=str(w.id)[-4:],
                                  values=(w.widget_type, w.config.get("text", "")[:15]))

    def on_tree_select(self, event):
        selected = self.widget_tree.selection()
        self.deselect_all()
        self.selected_widgets = list(selected)
        self.select_widgets(self.selected_widgets)

    def filter_widgets(self, query):
        # Фильтрация списка виджетов
        pass

    def load_templates(self):
        templates = ["Форма входа", "Калькулятор", "Таблица данных", "Настройки"]
        for t in templates:
            self.template_listbox.insert(tk.END, t)

    def insert_template(self, event):
        selection = self.template_listbox.curselection()
        if not selection:
            return

        template_name = self.template_listbox.get(selection[0])

        if template_name == "Форма входа":
            self.add_form_login()
        elif template_name == "Калькулятор":
            self.add_calculator()

        self.undo_manager.save_state(f"Вставлен шаблон: {template_name}")

    def add_form_login(self):
        # Добавление шаблона формы входа
        base_x, base_y = 100, 100
        self.current_widget_type = "Label"
        self.place_widget(base_x, base_y)
        self.widgets[-1].config["text"] = "Логин:"

        self.current_widget_type = "Entry"
        self.place_widget(base_x + 100, base_y)

        self.current_widget_type = "Label"
        self.place_widget(base_x, base_y + 40)
        self.widgets[-1].config["text"] = "Пароль:"

        self.current_widget_type = "Entry"
        self.place_widget(base_x + 100, base_y + 40)

        self.current_widget_type = "Button"
        self.place_widget(base_x + 50, base_y + 80)
        self.widgets[-1].config["text"] = "Войти"

        self.update_tree()

    def add_calculator(self):
        # Шаблон калькулятора
        pass

    def ai_generate(self):
        prompt = self.ai_entry.get()
        messagebox.showinfo("AI", f"Генерация по запросу: '{prompt}'\n(Здесь будет интеграция с LLM)")
        # Простая эмуляция
        if "форма" in prompt.lower() or "login" in prompt.lower():
            self.add_form_login()

    def preview(self):
        # Создание временного окна с текущим дизайном
        preview_win = tk.Toplevel(self.root)
        preview_win.title("Предпросмотр")
        preview_win.geometry("600x400")

        for w in self.widgets:
            try:
                tk_class = getattr(tk, w.widget_type, ttk)
                widget = tk_class(preview_win, **w.config)
                widget.place(x=w.x, y=w.y)

                # Привязка событий
                for evt, func_name in w.events.items():
                    if func_name:
                        # Эмуляция привязки
                        pass
            except Exception as e:
                print(f"Preview error: {e}")

    def generate_code(self):
        code = """import tkinter as tk
from tkinter import ttk

class GeneratedApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Generated App")
        self.root.geometry("800x600")

"""
        for w in self.widgets:
            var_name = f"self.{w.widget_type.lower()}_{str(w.id)[-4:]}"
            config_str = ", ".join([f'{k}="{v}"' if isinstance(v, str) else f'{k}={v}'
                                   for k, v in w.config.items() if v])

            code += f"        {var_name} = tk.{w.widget_type}(self.root, {config_str})\n"
            code += f"        {var_name}.place(x={int(w.x)}, y={int(w.y)})\n"

            # Генерация привязок событий
            for evt, func_name in w.events.items():
                if func_name:
                    code += f"        {var_name}.bind(\"{evt}\", self.{func_name})\n\n"

        code += """
if __name__ == "__main__":
    root = tk.Tk()
    app = GeneratedApp(root)
    root.mainloop()
"""
        top = tk.Toplevel(self.root)
        top.title("Код")
        top.geometry("700x500")

        text = tk.Text(top, font=("Consolas", 10))
        text.pack(fill=tk.BOTH, expand=True)
        text.insert(tk.END, code)

        btn_frame = ttk.Frame(top)
        btn_frame.pack(fill=tk.X, pady=5)

        def copy_code():
            self.root.clipboard_clear()
            self.root.clipboard_append(code)
            messagebox.showinfo("OK", "Код скопирован!")

        ttk.Button(btn_frame, text="Копировать", command=copy_code).pack(side=tk.LEFT, padx=10)
        ttk.Button(btn_frame, text="Закрыть", command=top.destroy).pack(side=tk.RIGHT, padx=10)

    def save_project(self):
        data = []
        for w in self.widgets:
            data.append({
                "type": w.widget_type,
                "x": w.x,
                "y": w.y,
                "config": w.config,
                "events": w.events
            })

        file_path = filedialog.asksaveasfilename(defaultextension=".json",
                                                 filetypes=[("JSON", "*.json")])
        if file_path:
            with open(file_path, 'w', encoding='utf-8') as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
            messagebox.showinfo("OK", "Проект сохранен!")

    def load_project(self):
        file_path = filedialog.askopenfilename(filetypes=[("JSON", "*.json")])
        if file_path:
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    data = json.load(f)

                self.canvas.delete("all")
                self.widgets = []
                self.deselect_all()

                for item in data:
                    w = WidgetItem(item["type"], item["x"], item["y"], item["config"])
                    w.events = item.get("events", {})
                    self.widgets.append(w)
                    self.render_widget(w)

                self.update_tree()
                messagebox.showinfo("OK", "Проект загружен!")
            except Exception as e:
                messagebox.showerror("Error", str(e))

    def restore_state(self, state):
        self.canvas.delete("all")
        self.widgets = []
        for item in state:
            w = WidgetItem(item["type"], item["x"], item["y"], item["config"])
            self.widgets.append(w)
            self.render_widget(w)
        self.update_tree()
        self.deselect_all()

    def update_status(self, msg):
        self.status_label.config(text=msg)

def main():
    root = tk.Tk()
    app = GUIBuilderApp(root)
    root.mainloop()

if __name__ == "__main__":
    main()