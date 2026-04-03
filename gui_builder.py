import tkinter as tk
from tkinter import ttk, messagebox, filedialog, colorchooser, simpledialog
import json
import copy
import time
import threading
import urllib.request
import urllib.error

# ─────────────────────────────────────────────────────────────────────────────
ICONS = {
    "Label": "🏷️",  "Button": "🔘",    "Entry": "📝",     "Checkbutton": "☑️",
    "Radiobutton": "🔘", "Listbox": "📋", "Text": "📄",  "Scale": "🎚️",
    "Canvas": "🎨",  "Frame": "🖼️",     "Notebook": "📑",  "PanedWindow": "⚖️",
    "Spinbox": "🔢", "Combobox": "📦",   "Progressbar": "📊","Scrollbar": "↕️",
    "Separator": "➖","Menubutton": "📂",
}

WIDGET_TOOLTIPS = {
    "Label":       "Отображает текст или изображение. Не интерактивен.",
    "Button":      "Кнопка — вызывает функцию при нажатии.",
    "Entry":       "Однострочное поле ввода текста.",
    "Checkbutton": "Чекбокс — вкл/выкл состояние.",
    "Radiobutton": "Один из группы взаимоисключающих вариантов.",
    "Listbox":     "Прокручиваемый список элементов.",
    "Text":        "Многострочное текстовое поле.",
    "Scale":       "Ползунок для выбора числового значения.",
    "Canvas":      "Холст для произвольной графики.",
    "Frame":       "Контейнер для группировки виджетов.",
    "Notebook":    "Вкладки — несколько панелей.",
    "PanedWindow": "Разделитель с изменяемым размером панелей.",
    "Spinbox":     "Числовое поле с кнопками▲▼.",
    "Combobox":    "Выпадающий список + поле ввода.",
    "Progressbar": "Полоса прогресса выполнения.",
    "Scrollbar":   "Полоса прокрутки для виджетов.",
    "Separator":   "Горизонтальная/вертикальная линия-разделитель.",
    "Menubutton":  "Кнопка, открывающая выпадающее меню.",
}

WIDGET_TYPES = [
    ("Label","Текст"),("Button","Кнопка"),("Entry","Ввод"),
    ("Checkbutton","Чекбокс"),("Radiobutton","Радио"),("Listbox","Список"),
    ("Text","Текст↕"),("Scale","Ползунок"),("Canvas","Холст"),
    ("Frame","Фрейм"),("Notebook","Вкладки"),("PanedWindow","Панель"),
    ("Spinbox","Счётчик"),("Combobox","Выпадающий"),("Progressbar","Прогресс"),
    ("Scrollbar","Скролл"),("Separator","Разделитель"),("Menubutton","Меню↓"),
]


# ─────────────────────────────────────────────────────────────────────────────
class Tooltip:
    def __init__(self, widget, text):
        self.widget = widget
        self.text   = text
        self.tip    = None
        widget.bind("<Enter>", self._show, "+")
        widget.bind("<Leave>", self._hide, "+")

    def _show(self, _=None):
        if self.tip:
            return
        x = self.widget.winfo_rootx() + self.widget.winfo_width() + 4
        y = self.widget.winfo_rooty()
        self.tip = tk.Toplevel(self.widget)
        self.tip.wm_overrideredirect(True)
        self.tip.wm_geometry(f"+{x}+{y}")
        tk.Label(self.tip, text=self.text, bg="#fffbe6", fg="#333",
                 relief="solid", bd=1, font=("Arial", 8),
                 wraplength=180, justify="left", padx=5, pady=3).pack()

    def _hide(self, _=None):
        if self.tip:
            self.tip.destroy()
            self.tip = None


# ─────────────────────────────────────────────────────────────────────────────
class UndoManager:
    def __init__(self, app):
        self.app       = app
        self.undo_stack = []
        self.redo_stack = []
        self.max_steps  = 50
        self.on_change  = None

    def _snap(self):
        data = []
        for w in self.app.widgets:
            data.append({
                "type": w.widget_type, "x": w.x, "y": w.y,
                "config": w.config.copy(), "events": w.events.copy(),
                "parent_id": w.parent_id,
                "group_id":  getattr(w, "group_id",  None),
                "visible":   getattr(w, "visible",   True),
                "locked":    getattr(w, "locked",    False),
            })
        return {"widgets": data,
                "current_container": getattr(self.app, "current_container_id", None)}

    def save_state(self, action=""):
        if len(self.undo_stack) >= self.max_steps:
            self.undo_stack.pop(0)
        self.undo_stack.append((action, self._snap()))
        self.redo_stack.clear()
        self.app.update_status(f"✔ {action}")
        if self.on_change:
            self.on_change()

    def undo(self):
        if not self.undo_stack:
            return
        action, state = self.undo_stack.pop()
        self.redo_stack.append((action, self._snap()))
        self.app.restore_state(state)
        self.app.update_status(f"↩ Отменено: {action}")
        if self.on_change:
            self.on_change()

    def redo(self):
        if not self.redo_stack:
            return
        action, state = self.redo_stack.pop()
        self.undo_stack.append((action, self._snap()))
        self.app.restore_state(state)
        self.app.update_status(f"↪ Повторено: {action}")
        if self.on_change:
            self.on_change()


# ─────────────────────────────────────────────────────────────────────────────
class WidgetItem:
    def __init__(self, widget_type, x, y, config, parent_id=None):
        self.widget_type     = widget_type
        self.x, self.y       = x, y
        self.config          = config
        self.parent_id       = parent_id
        self.widget_instance = None
        self.frame           = None   # direct ref for resize
        self.id              = id(self)
        self.events          = {}
        self.selection_rect  = None
        self.resize_handles  = []
        self.group_id        = None
        self.visible         = True
        self.locked          = False
        self.current_width   = 80
        self.current_height  = 28

    def get_size(self):
        return self.current_width, self.current_height


# ─────────────────────────────────────────────────────────────────────────────
class GUIBuilderApp:
    def __init__(self, root):
        self.root = root
        self.root.title("🚀 Ultimate Tkinter Constructor")
        self.root.geometry("1500x920")
        ttk.Style().theme_use("clam")
        self.screens = {}  # Словарь для хранения экранов {name: [widgets]}
        self.current_screen = "main"
        self.screen_transitions = []  # Переходы между экранами
        self.widgets          = []
        self.selected_widgets = []
        self.drag_data        = {"items":[], "start_x":0, "start_y":0,
                                 "resizing":False, "resize_widget":None,
                                 "resize_handle_idx":None}
        self.nav_panel = None
        self.clipboard        = None
        self.current_mode     = "move"
        self.current_widget_type = None
        self.snap_to_grid     = True
        self.grid_size        = 10
        self.current_container_id = None
        self.pan_start        = None
        self.zoom_level       = 1.0

        self.guides           = []    # [{'type':'v'/'h','pos':int,'id':canvas_id}]
        self.dragging_guide   = None
        self.temp_guide_id    = None
        self.temp_guide_type  = None
        self.temp_guide_pos   = 0

        self.api_key          = ""
        self.api_provider     = "deepseek"
        self.minimap_canvas   = None

        self.undo_manager = UndoManager(self)
        self.undo_manager.on_change = self._refresh_history

        self.setup_ui()
        self.bind_keys()
        self.load_templates()
        self.root.after(250, self._init_minimap)

    def _set_api_key(self):
        """Установка API ключа (DeepSeek или Anthropic)"""
        win = tk.Toplevel(self.root)
        win.title("🔑 Настройка API")
        win.geometry("400x250")
        win.transient(self.root)

        ttk.Label(win, text="Выберите API провайдера:", font=("Arial", 10, "bold")).pack(pady=10)

        provider_var = tk.StringVar(value="deepseek")
        ttk.Radiobutton(win, text="DeepSeek (рекомендуется)", variable=provider_var, value="deepseek").pack(anchor=tk.W,
                                                                                                            padx=20)
        ttk.Radiobutton(win, text="Anthropic Claude", variable=provider_var, value="anthropic").pack(anchor=tk.W,
                                                                                                     padx=20)

        ttk.Label(
            win,
            text="Ключ DeepSeek: https://platform.deepseek.com/",
            foreground="blue",
            cursor="hand2",
        ).pack(anchor=tk.W, padx=20, pady=(4, 0))

        ttk.Label(win, text="API ключ:").pack(anchor=tk.W, padx=20, pady=(10, 0))
        key_entry = ttk.Entry(win, width=40, show="*")
        key_entry.pack(padx=20, pady=5)
        key_entry.insert(0, self.api_key if hasattr(self, 'api_key') else "")

        def save():
            self.api_provider = provider_var.get()
            self.api_key = key_entry.get().strip()
            win.destroy()
            self.update_status(f"✓ API ключ сохранен ({self.api_provider})")

        ttk.Button(win, text="💾 Сохранить", command=save).pack(pady=15)

    def ai_generate_multi_screen(self, prompt):
        """Генерация многоэкранного интерфейса через DeepSeek API"""
        if not self.api_key:
            messagebox.showwarning("API", "Сначала настройте ключ: верхняя панель → «🔑 API»")
            return

        self.update_status("🤖 Генерирую многоэкранный интерфейс...")

        system_prompt = """Ты эксперт по созданию GUI интерфейсов на Tkinter. 
        Сгенерируй JSON с несколькими экранами для следующего описания.

        Формат ответа (ТОЛЬКО JSON, без пояснений):
        {
            "screens": [
                {
                    "name": "login",
                    "title": "Вход",
                    "widgets": [
                        {"type": "Label", "x": 100, "y": 50, "config": {"text": "Логин", "bg": "#f0f0f0"}},
                        {"type": "Entry", "x": 200, "y": 50, "config": {"width": 20}},
                        {"type": "Button", "x": 150, "y": 150, "config": {"text": "Далее"}}
                    ]
                }
            ],
            "transitions": [
                {"from": "login", "to": "register", "trigger_widget": "Button"}
            ]
        }

        Координаты x и y: 50-500.
        Используй понятные имена экранов: login, register, forgot_password, verify_email.
        Добавь кнопки навигации: "Назад", "Далее", "Отправить".
        """

        full_prompt = f"Создай интерфейс: {prompt}. Включи экраны: главный, забыли пароль, подтверждение почты, регистрация. Добавь кнопки для навигации между экранами."

        try:
            result = self._call_deepseek_api(system_prompt, full_prompt)
            self._apply_multi_screen_generation(result)
        except Exception as e:
            messagebox.showerror("Ошибка", f"DeepSeek ошибка: {str(e)}")
            self.update_status("❌ Ошибка генерации")

    def _call_deepseek_api(self, system_prompt, user_prompt):
        """Вызов DeepSeek API"""
        import urllib.request
        import urllib.error
        import json

        url = "https://api.deepseek.com/v1/chat/completions"

        headers = {
            "Content-Type": "application/json",
            "Authorization": f"Bearer {self.api_key}"
        }

        data = {
            "model": "deepseek-chat",
            "messages": [
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt}
            ],
            "temperature": 0.7,
            "max_tokens": 4000
        }

        req = urllib.request.Request(
            url,
            data=json.dumps(data).encode(),
            headers=headers,
            method="POST"
        )

        with urllib.request.urlopen(req, timeout=60) as response:
            result = json.loads(response.read().decode())
            return result["choices"][0]["message"]["content"]

    def _call_ai_api(self, system_prompt, user_prompt):
        """Единая точка вызова ИИ (DeepSeek или Anthropic)."""
        if getattr(self, "api_provider", "deepseek") == "anthropic":
            return self._call_anthropic_api(system_prompt, user_prompt)
        return self._call_deepseek_api(system_prompt, user_prompt)

    def _build_ai_preview_context(self, preview_screen_name=None):
        """Текстовое описание проекта для ИИ: экраны, виджеты, логика."""
        lines = ["=== Контекст конструктора (предпросмотр) ==="]
        if preview_screen_name:
            lines.append(f"Активный экран в окне предпросмотра: {preview_screen_name}")
        else:
            lines.append("Режим: один холст без разбиения на экраны.")
        if self.screens:
            for sn, wlist in self.screens.items():
                lines.append(f"\n--- Экран «{sn}» ({len(wlist)} виджетов) ---")
                for wo in wlist:
                    if not getattr(wo, "visible", True):
                        continue
                    t = (wo.config.get("text") or "")[:100]
                    lines.append(
                        f"  id={wo.id} | {wo.widget_type} | pos=({wo.x},{wo.y}) | "
                        f"size=({wo.current_width}x{wo.current_height}) | text={t!r} | events={wo.events}"
                    )
        else:
            lines.append("\n--- Виджеты на холсте ---")
            for wo in self.widgets:
                if not wo.visible:
                    continue
                t = (wo.config.get("text") or "")[:100]
                lines.append(
                    f"  id={wo.id} | {wo.widget_type} | pos=({wo.x},{wo.y}) | "
                    f"size=({wo.current_width}x{wo.current_height}) | text={t!r} | events={wo.events}"
                )
        if self.logic_rules:
            lines.append("\n--- Правила логики (ключ = id виджета-источника) ---")
            try:
                lines.append(json.dumps(self.logic_rules, ensure_ascii=False, indent=2))
            except Exception:
                lines.append(str(self.logic_rules))
        if self.screen_transitions:
            lines.append("\n--- Переходы между экранами (из AI-генерации) ---")
            lines.append(json.dumps(self.screen_transitions, ensure_ascii=False, indent=2))
        return "\n".join(lines)

    def _preview_ai_send(self, win, screen_state, q_widget, a_widget):
        """Отправка вопроса в ИИ из окна предпросмотра (в фоне)."""
        q = q_widget.get("1.0", "end-1c").strip()
        if not q:
            messagebox.showinfo("ИИ", "Введите вопрос.")
            return
        if not self.api_key:
            messagebox.showwarning("API", "Сначала укажите ключ: верхняя панель → «🔑 API».")
            return

        a_widget.config(state=tk.NORMAL)
        a_widget.delete("1.0", tk.END)
        a_widget.insert(tk.END, "Запрос к ИИ…")
        a_widget.config(state=tk.DISABLED)
        win.update_idletasks()

        ctx = self._build_ai_preview_context(screen_state.get("name"))
        system = """Ты помощник в визуальном конструкторе интерфейсов на Tkinter.
Пользователь смотрит предпросмотр: могут быть несколько экранов, простые и сложные виджеты (Entry, Text, Combobox, Scale и т.д.).
Помоги с логикой форм, валидацией, сравнением полей, навигацией между экранами, выбором виджетов, UX.
Отвечай по-русски. Если даёшь шаги в конструкторе — нумеруй. Код давай только если уместно, кратко."""

        user = f"Вопрос:\n{q}\n\n{ctx}"

        def work():
            try:
                result = self._call_ai_api(system, user)

                def done():
                    a_widget.config(state=tk.NORMAL)
                    a_widget.delete("1.0", tk.END)
                    a_widget.insert(tk.END, result)
                    a_widget.config(state=tk.DISABLED)

                win.after(0, done)
            except Exception as e:

                def err():
                    a_widget.config(state=tk.NORMAL)
                    a_widget.delete("1.0", tk.END)
                    a_widget.insert(tk.END, f"Ошибка: {e}")
                    a_widget.config(state=tk.DISABLED)

                win.after(0, err)

        threading.Thread(target=work, daemon=True).start()

    def attach_preview_ai_panel(self, win, screen_state, parent=None):
        """Панель чата с ИИ в окне предпросмотра. parent — контейнер (например нижняя часть PanedWindow)."""
        root = parent if parent is not None else win
        ai = ttk.LabelFrame(
            root,
            text="🤖 ИИ-помощник (видит экраны, id виджетов и правила логики)",
            padding=6,
        )
        ai.pack(fill=tk.BOTH, expand=True, padx=4, pady=4)

        q = tk.Text(ai, height=3, font=("Arial", 10), wrap=tk.WORD)
        q.pack(fill=tk.X, pady=(0, 4))
        hint = (
            "Примеры: «Как проверить совпадение паролей?», «Что добавить на экран регистрации?», "
            "«Как связать кнопку с другим экраном?»"
        )
        ttk.Label(ai, text=hint, font=("Arial", 8), foreground="gray").pack(anchor=tk.W)

        ttk.Label(ai, text="Ответ:", font=("Arial", 9, "bold")).pack(anchor=tk.W, pady=(6, 0))
        a = tk.Text(ai, height=10, font=("Consolas", 9), wrap=tk.WORD, state=tk.DISABLED)
        a.pack(fill=tk.BOTH, expand=True, pady=4)

        bf = ttk.Frame(ai)
        bf.pack(fill=tk.X)
        ttk.Button(
            bf,
            text="Спросить ИИ",
            command=lambda: self._preview_ai_send(win, screen_state, q, a),
        ).pack(side=tk.LEFT, padx=2)

        def quick_tip():
            q.delete("1.0", tk.END)
            q.insert(
                tk.END,
                "Дай краткий совет по UX и логике для текущего экрана предпросмотра: "
                "что улучшить и какие виджеты/правила логики добавить.",
            )

        ttk.Button(bf, text="Шаблон: совет по экрану", command=quick_tip).pack(side=tk.LEFT, padx=2)

    def _call_anthropic_api(self, system_prompt, user_prompt):
        """Вызов Anthropic API (существующий метод)"""
        # Используем ваш существующий код для Anthropic
        import urllib.request
        import json

        url = "https://api.anthropic.com/v1/messages"
        headers = {
            "Content-Type": "application/json",
            "x-api-key": self.api_key,
            "anthropic-version": "2023-06-01"
        }

        data = {
            "model": "claude-3-sonnet-20240229",
            "max_tokens": 4000,
            "system": system_prompt,
            "messages": [{"role": "user", "content": user_prompt}]
        }

        req = urllib.request.Request(
            url,
            data=json.dumps(data).encode(),
            headers=headers,
            method="POST"
        )

        with urllib.request.urlopen(req, timeout=60) as response:
            result = json.loads(response.read().decode())
            return result["content"][0]["text"]

    def _apply_multi_screen_generation(self, ai_response):
        """Применяет сгенерированные экраны"""
        import re
        import json

        # Очищаем ответ от markdown
        text = ai_response.strip()
        if "```json" in text:
            text = text.split("```json")[1].split("```")[0]
        elif "```" in text:
            text = text.split("```")[1].split("```")[0]

        try:
            data = json.loads(text)
            screens = data.get("screens", [])
            transitions = data.get("transitions", [])

            # Сохраняем текущие виджеты как экран "main"
            if self.widgets and "main" not in self.screens:
                self.screens["main"] = self.widgets.copy()

            # Создаем новые экраны
            for screen in screens:
                screen_name = screen["name"]
                screen_widgets = []

                for wdata in screen["widgets"]:
                    wt = wdata["type"]
                    x = wdata.get("x", 100)
                    y = wdata.get("y", 100)
                    cfg = wdata.get("config", {})

                    # Создаем виджет
                    nw = WidgetItem(wt, x, y, cfg)
                    screen_widgets.append(nw)

                self.screens[screen_name] = screen_widgets

            # Сохраняем переходы
            self.screen_transitions = transitions

            # Показываем первый экран
            if screens:
                self.switch_to_screen(screens[0]["name"])

            # Добавляем панель навигации по экранам
            self.add_screen_navigation()

            self.update_status(f"✓ Создано {len(screens)} экранов")

        except json.JSONDecodeError as e:
            messagebox.showerror("Ошибка", f"Не удалось распарсить ответ AI:\n{text[:500]}")
            print(f"JSON Error: {e}\nResponse: {text}")

    def add_screen_navigation(self):
        """Добавляет панель навигации по экранам"""
        # Проверяем, есть ли уже панель
        if hasattr(self, 'screen_panel') and self.screen_panel:
            return

        # Создаем панель в правом верхнем углу
        self.screen_panel = tk.Frame(self.root, bg="#2c3e50", relief=tk.RAISED, bd=1)
        self.screen_panel.place(relx=1.0, x=-10, y=10, anchor="ne")

        tk.Label(self.screen_panel, text="📱 Экраны", bg="#2c3e50", fg="white",
                 font=("Arial", 9, "bold")).pack(padx=10, pady=5)

        # Кнопки для каждого экрана
        for screen_name in self.screens.keys():
            btn = tk.Button(
                self.screen_panel,
                text=f"📺 {screen_name}",
                bg="#34495e",
                fg="white",
                relief=tk.FLAT,
                command=lambda n=screen_name: self.switch_to_screen(n)
            )
            btn.pack(fill=tk.X, padx=5, pady=2)

            # Подсветка активного экрана
            if screen_name == self.current_screen:
                btn.config(bg="#1abc9c")

    def switch_to_screen(self, screen_name):
        """Переключается на указанный экран"""
        if screen_name not in self.screens:
            messagebox.showerror("Ошибка", f"Экран '{screen_name}' не найден")
            return

        # Сохраняем текущий экран если есть виджеты
        if self.widgets:
            self.screens[self.current_screen] = self.widgets.copy()

        # Очищаем холст
        self.canvas.delete("all")
        self.widgets = []
        self.selected_widgets = []

        # Загружаем новый экран
        for wo in self.screens[screen_name]:
            # Создаем копию виджета
            nw = WidgetItem(wo.widget_type, wo.x, wo.y, wo.config.copy())
            nw.current_width = wo.current_width
            nw.current_height = wo.current_height
            nw.events = wo.events.copy()
            nw.visible = wo.visible
            nw.locked = wo.locked
            self.widgets.append(nw)
            self.render_widget(nw)

        self.current_screen = screen_name
        self.draw_grid()
        self.update_layer_panel()
        self.update_logic_panel()
        self._update_minimap()

        # Обновляем подсветку в панели навигации
        if hasattr(self, 'screen_panel'):
            for child in self.screen_panel.winfo_children():
                if isinstance(child, tk.Button):
                    if child.cget("text") == f"📺 {screen_name}":
                        child.config(bg="#1abc9c")
                    else:
                        child.config(bg="#34495e")

        self.update_status(f"📱 Переключено на экран: {screen_name}")

    def add_new_screen(self):
        """Создает новый пустой экран"""
        from tkinter import simpledialog

        name = simpledialog.askstring("Новый экран", "Введите имя экрана:")
        if name and name not in self.screens:
            self.screens[name] = []
            self.add_screen_navigation()
            self.switch_to_screen(name)
            self.update_status(f"✓ Создан экран: {name}")
        elif name in self.screens:
            messagebox.showwarning("Внимание", "Экран с таким именем уже существует")

    def delete_current_screen(self):
        """Удаляет текущий экран"""
        if self.current_screen == "main":
            if not messagebox.askyesno("Подтверждение", "Удалить главный экран?"):
                return

        if messagebox.askyesno("Подтверждение", f"Удалить экран '{self.current_screen}'?"):
            del self.screens[self.current_screen]

            # Переключаемся на первый доступный экран
            if self.screens:
                first_screen = list(self.screens.keys())[0]
                self.switch_to_screen(first_screen)
            else:
                # Создаем пустой экран
                self.screens["main"] = []
                self.switch_to_screen("main")

            # Обновляем навигацию
            if hasattr(self, 'screen_panel'):
                self.screen_panel.destroy()
                delattr(self, 'screen_panel')
            self.add_screen_navigation()

            self.update_status(f"✓ Удален экран: {self.current_screen}")

    def create_registration_flow(self):
        """Создает готовый поток регистрации с 4 экранами"""

        # Очищаем старые экраны
        self.screens = {}

        # ========== ЭКРАН 1: ВХОД ==========
        screen_login = []
        screen_login.append(WidgetItem("Label", 200, 30, {"text": "🔐 Добро пожаловать", "bg": "#2c3e50", "fg": "white",
                                                          "font": "Arial 14 bold"}))
        screen_login.append(WidgetItem("Label", 100, 100, {"text": "Email:", "bg": "#f0f0f0"}))
        screen_login.append(WidgetItem("Entry", 200, 100, {"width": 25, "bg": "white"}))
        screen_login.append(WidgetItem("Label", 100, 150, {"text": "Пароль:", "bg": "#f0f0f0"}))
        screen_login.append(WidgetItem("Entry", 200, 150, {"width": 25, "bg": "white", "show": "*"}))
        screen_login.append(WidgetItem("Button", 150, 200, {"text": "Войти", "bg": "#27ae60", "fg": "white"}))

        forgot_btn = WidgetItem("Button", 120, 240, {"text": "❓ Забыли пароль?", "bg": "#f0f0f0", "fg": "#2980b9"})
        forgot_btn.events["<Button-1>"] = "switch_screen('forgot_password')"
        screen_login.append(forgot_btn)

        register_btn = WidgetItem("Button", 120, 270, {"text": "📝 Регистрация", "bg": "#f0f0f0", "fg": "#2980b9"})
        register_btn.events["<Button-1>"] = "switch_screen('register')"
        screen_login.append(register_btn)

        # ========== ЭКРАН 2: ЗАБЫЛИ ПАРОЛЬ ==========
        screen_forgot = []
        screen_forgot.append(WidgetItem("Label", 180, 30,
                                        {"text": "🔐 Восстановление пароля", "bg": "#2c3e50", "fg": "white",
                                         "font": "Arial 12 bold"}))
        screen_forgot.append(WidgetItem("Label", 100, 100, {"text": "Ваш Email:", "bg": "#f0f0f0"}))
        screen_forgot.append(WidgetItem("Entry", 220, 100, {"width": 25, "bg": "white"}))
        screen_forgot.append(
            WidgetItem("Button", 180, 160, {"text": "📧 Отправить код", "bg": "#3498db", "fg": "white"}))

        back_btn1 = WidgetItem("Button", 180, 200, {"text": "◀ Назад к входу", "bg": "#95a5a6", "fg": "white"})
        back_btn1.events["<Button-1>"] = "switch_screen('login')"
        screen_forgot.append(back_btn1)

        # ========== ЭКРАН 3: ПОДТВЕРЖДЕНИЕ ==========
        screen_verify = []
        screen_verify.append(WidgetItem("Label", 180, 30,
                                        {"text": "📧 Подтверждение почты", "bg": "#2c3e50", "fg": "white",
                                         "font": "Arial 12 bold"}))
        screen_verify.append(WidgetItem("Label", 100, 100, {"text": "Код из письма:", "bg": "#f0f0f0"}))
        screen_verify.append(WidgetItem("Entry", 220, 100, {"width": 15, "bg": "white"}))
        screen_verify.append(WidgetItem("Button", 180, 160, {"text": "✅ Подтвердить", "bg": "#27ae60", "fg": "white"}))

        # ========== ЭКРАН 4: РЕГИСТРАЦИЯ ==========
        screen_register = []
        screen_register.append(WidgetItem("Label", 200, 20, {"text": "📝 Регистрация", "bg": "#2c3e50", "fg": "white",
                                                             "font": "Arial 12 bold"}))
        screen_register.append(WidgetItem("Label", 80, 70, {"text": "Имя:", "bg": "#f0f0f0"}))
        screen_register.append(WidgetItem("Entry", 200, 70, {"width": 25, "bg": "white"}))
        screen_register.append(WidgetItem("Label", 80, 110, {"text": "Email:", "bg": "#f0f0f0"}))
        screen_register.append(WidgetItem("Entry", 200, 110, {"width": 25, "bg": "white"}))
        screen_register.append(WidgetItem("Label", 80, 150, {"text": "Пароль:", "bg": "#f0f0f0"}))
        screen_register.append(WidgetItem("Entry", 200, 150, {"width": 25, "bg": "white", "show": "*"}))
        screen_register.append(WidgetItem("Label", 80, 190, {"text": "Подтверждение:", "bg": "#f0f0f0"}))
        screen_register.append(WidgetItem("Entry", 200, 190, {"width": 25, "bg": "white", "show": "*"}))
        screen_register.append(
            WidgetItem("Button", 150, 240, {"text": "📝 Зарегистрироваться", "bg": "#27ae60", "fg": "white"}))

        back_btn2 = WidgetItem("Button", 150, 280, {"text": "◀ Назад ко входу", "bg": "#95a5a6", "fg": "white"})
        back_btn2.events["<Button-1>"] = "switch_screen('login')"
        screen_register.append(back_btn2)

        # Сохраняем экраны
        self.screens = {
            "login": screen_login,
            "forgot_password": screen_forgot,
            "verify_email": screen_verify,
            "register": screen_register
        }

        self.current_screen = "login"

        # СОЗДАЕМ ПАНЕЛЬ ТОЛЬКО ОДИН РАЗ
        self.create_screen_navigation_panel()

        # Отображаем первый экран
        self.display_current_screen()

        messagebox.showinfo("Успех", "Создано 4 экрана!\nИспользуйте панель '📱 ЭКРАНЫ' справа для переключения.")
        self.update_status("✓ Создано 4 экрана с навигацией!")

    def create_order_form(self):
        """Создает форму заказа"""
        widgets = []

        y = 50
        fields = ["Товар:", "Количество:", "Цена:", "Адрес доставки:", "Телефон:"]

        for field in fields:
            widgets.append(WidgetItem("Label", 80, y, {"text": field, "bg": "#f0f0f0"}))
            widgets.append(WidgetItem("Entry", 200, y, {"width": 30, "bg": "white"}))
            y += 40

        widgets.append(WidgetItem("Button", 150, y + 20, {"text": "🛒 Оформить заказ", "bg": "#27ae60", "fg": "white"}))
        widgets.append(WidgetItem("Button", 150, y + 60, {"text": "❌ Отмена", "bg": "#e74c3c", "fg": "white"}))

        self.screens["order_form"] = widgets
        self.add_screen_navigation()
        self.switch_to_screen("order_form")
        self.update_status("✓ Создана форма заказа")

    def create_chat_interface(self):
        """Создает интерфейс чата"""
        widgets = []

        widgets.append(
            WidgetItem("Label", 100, 30, {"text": "💬 Чат", "bg": "#2c3e50", "fg": "white", "font": "Arial 14 bold"}))
        widgets.append(WidgetItem("Text", 80, 70, {"width": 50, "height": 15, "bg": "#f5f5f5"}))
        widgets.append(WidgetItem("Entry", 80, 320, {"width": 40, "bg": "white"}))
        widgets.append(WidgetItem("Button", 420, 318, {"text": "📤 Отправить", "bg": "#3498db", "fg": "white"}))

        self.screens["chat"] = widgets
        self.add_screen_navigation()
        self.switch_to_screen("chat")
        self.update_status("✓ Создан чат интерфейс")

    def create_dashboard(self):
        """Создает панель управления"""
        widgets = []

        widgets.append(WidgetItem("Label", 100, 30, {"text": "📊 Панель управления", "bg": "#2c3e50", "fg": "white",
                                                     "font": "Arial 14 bold"}))
        widgets.append(WidgetItem("Frame", 80, 80, {"bg": "#ecf0f1", "width": 200, "height": 100}))
        widgets.append(WidgetItem("Label", 120, 120, {"text": "Пользователей: 1,234", "bg": "#ecf0f1"}))
        widgets.append(WidgetItem("Frame", 300, 80, {"bg": "#ecf0f1", "width": 200, "height": 100}))
        widgets.append(WidgetItem("Label", 340, 120, {"text": "Продаж: $12,345", "bg": "#ecf0f1"}))
        widgets.append(WidgetItem("Progressbar", 80, 210, {"value": 65, "length": 420, "mode": "determinate"}))
        widgets.append(WidgetItem("Label", 80, 240, {"text": "Прогресс: 65%", "bg": "white"}))

        self.screens["dashboard"] = widgets
        self.add_screen_navigation()
        self.switch_to_screen("dashboard")
        self.update_status("✓ Создана панель управления")

    def create_registration_flow(self):
        """Создает готовый поток регистрации с 4 экранами и рабочими кнопками"""

        # Очищаем старые экраны
        self.screens = {}

        # ========== ЭКРАН 1: ВХОД ==========
        screen_login = []

        # Заголовок
        title = WidgetItem("Label", 200, 30,
                           {"text": "🔐 Добро пожаловать", "bg": "#2c3e50", "fg": "white", "font": "Arial 14 bold"})
        title.current_width = 250
        title.current_height = 40
        screen_login.append(title)

        # Поля ввода
        screen_login.append(WidgetItem("Label", 100, 100, {"text": "Email:", "bg": "#f0f0f0"}))
        email_entry = WidgetItem("Entry", 200, 100, {"width": 25, "bg": "white"})
        screen_login.append(email_entry)

        screen_login.append(WidgetItem("Label", 100, 150, {"text": "Пароль:", "bg": "#f0f0f0"}))
        pass_entry = WidgetItem("Entry", 200, 150, {"width": 25, "bg": "white", "show": "*"})
        screen_login.append(pass_entry)

        # Кнопки с командами
        login_btn = WidgetItem("Button", 150, 200, {"text": "Войти", "bg": "#27ae60", "fg": "white"})
        login_btn.events["<Button-1>"] = "show_message('Вход выполнен')"
        screen_login.append(login_btn)

        forgot_btn = WidgetItem("Button", 130, 240, {"text": "❓ Забыли пароль?", "bg": "#f0f0f0", "fg": "#2980b9"})
        forgot_btn.events["<Button-1>"] = "switch_screen('forgot_password')"
        screen_login.append(forgot_btn)

        register_btn = WidgetItem("Button", 130, 270, {"text": "📝 Регистрация", "bg": "#f0f0f0", "fg": "#2980b9"})
        register_btn.events["<Button-1>"] = "switch_screen('register')"
        screen_login.append(register_btn)

        # ========== ЭКРАН 2: ЗАБЫЛИ ПАРОЛЬ ==========
        screen_forgot = []

        forgot_title = WidgetItem("Label", 180, 50, {"text": "🔐 Восстановление пароля", "bg": "#2c3e50", "fg": "white",
                                                     "font": "Arial 12 bold"})
        forgot_title.current_width = 280
        forgot_title.current_height = 40
        screen_forgot.append(forgot_title)

        screen_forgot.append(WidgetItem("Label", 100, 120, {"text": "Ваш Email:", "bg": "#f0f0f0"}))
        forgot_email = WidgetItem("Entry", 220, 120, {"width": 25, "bg": "white"})
        screen_forgot.append(forgot_email)

        send_btn = WidgetItem("Button", 180, 180, {"text": "📧 Отправить код", "bg": "#3498db", "fg": "white"})
        send_btn.events["<Button-1>"] = "switch_screen('verify_email')"
        screen_forgot.append(send_btn)

        back_btn1 = WidgetItem("Button", 180, 220, {"text": "◀ Назад", "bg": "#95a5a6", "fg": "white"})
        back_btn1.events["<Button-1>"] = "switch_screen('login')"
        screen_forgot.append(back_btn1)

        # ========== ЭКРАН 3: ПОДТВЕРЖДЕНИЕ ==========
        screen_verify = []

        verify_title = WidgetItem("Label", 180, 50, {"text": "📧 Подтверждение почты", "bg": "#2c3e50", "fg": "white",
                                                     "font": "Arial 12 bold"})
        verify_title.current_width = 280
        verify_title.current_height = 40
        screen_verify.append(verify_title)

        screen_verify.append(WidgetItem("Label", 100, 120, {"text": "Код из письма:", "bg": "#f0f0f0"}))
        code_entry = WidgetItem("Entry", 220, 120, {"width": 15, "bg": "white"})
        screen_verify.append(code_entry)

        verify_btn = WidgetItem("Button", 180, 180, {"text": "✅ Подтвердить", "bg": "#27ae60", "fg": "white"})
        verify_btn.events["<Button-1>"] = "show_message('Почта подтверждена!')"
        screen_verify.append(verify_btn)

        # ========== ЭКРАН 4: РЕГИСТРАЦИЯ ==========
        screen_register = []

        reg_title = WidgetItem("Label", 200, 30,
                               {"text": "📝 Регистрация", "bg": "#2c3e50", "fg": "white", "font": "Arial 12 bold"})
        reg_title.current_width = 200
        reg_title.current_height = 40
        screen_register.append(reg_title)

        # Поля регистрации
        y_pos = 80
        fields = [("Имя:", 80), ("Email:", 130), ("Пароль:", 180), ("Подтверждение:", 230)]

        for label_text, y in fields:
            screen_register.append(WidgetItem("Label", 100, y, {"text": label_text, "bg": "#f0f0f0"}))
            entry = WidgetItem("Entry", 220, y, {"width": 25, "bg": "white"})
            if "Пароль" in label_text:
                entry.config["show"] = "*"
            screen_register.append(entry)

        reg_btn = WidgetItem("Button", 180, 290, {"text": "📝 Зарегистрироваться", "bg": "#27ae60", "fg": "white"})
        reg_btn.events["<Button-1>"] = "show_message('Регистрация успешна!')"
        screen_register.append(reg_btn)

        back_btn2 = WidgetItem("Button", 180, 330, {"text": "◀ Назад", "bg": "#95a5a6", "fg": "white"})
        back_btn2.events["<Button-1>"] = "switch_screen('login')"
        screen_register.append(back_btn2)

        # Сохраняем экраны
        self.screens = {
            "login": screen_login,
            "forgot_password": screen_forgot,
            "verify_email": screen_verify,
            "register": screen_register
        }

        self.current_screen = "login"

        # Создаем панель навигации
        self.create_screen_navigation_panel()

        # Отображаем первый экран
        self.display_current_screen()

        self.update_status("✓ Создано 4 экрана с навигацией!")

    def add_screen_navigation(self):
        """УСТАРЕВШИЙ МЕТОД - не использовать"""
        pass  # Пустой метод для совместимости

    def create_screen_navigation_panel(self):
        """Создает панель с кнопками переключения экранов - ЕДИНСТВЕННЫЙ МЕТОД"""
        # Полностью уничтожаем ВСЕ старые панели
        if hasattr(self, 'nav_panel') and self.nav_panel is not None:
            try:
                self.nav_panel.destroy()
            except:
                pass
            self.nav_panel = None

        if hasattr(self, 'screen_panel') and self.screen_panel is not None:
            try:
                self.screen_panel.destroy()
            except:
                pass
            self.screen_panel = None

        # Если нет экранов - выходим
        if not self.screens:
            return

        # Создаем новую панель
        self.nav_panel = tk.Frame(self.root, bg="#2c3e50", relief=tk.RAISED, bd=2)
        self.nav_panel.place(relx=1.0, x=-10, y=50, anchor="ne")

        # Заголовок
        title_label = tk.Label(self.nav_panel, text="📱 ЭКРАНЫ", bg="#2c3e50", fg="white",
                               font=("Arial", 9, "bold"))
        title_label.pack(padx=10, pady=5, fill=tk.X)

        # Разделитель
        sep = tk.Frame(self.nav_panel, bg="#1abc9c", height=2)
        sep.pack(fill=tk.X, padx=5, pady=2)

        # Кнопки для каждого экрана
        names = {
            "login": "🔐 Вход",
            "forgot_password": "❓ Забыли пароль",
            "verify_email": "📧 Подтверждение",
            "register": "📝 Регистрация",
            "order_form": "🛒 Заказ",
            "chat": "💬 Чат",
            "dashboard": "📊 Дашборд",
            "main": "🏠 Главный"
        }

        for screen_key in self.screens.keys():
            btn_text = names.get(screen_key, f"📄 {screen_key}")
            is_current = screen_key == self.current_screen
            btn = tk.Button(
                self.nav_panel,
                text=btn_text,
                bg="#1abc9c" if is_current else "#34495e",
                fg="white",
                relief=tk.FLAT,
                cursor="hand2",
                font=("Arial", 8),
                command=lambda k=screen_key: self.switch_to_screen_direct(k)
            )
            btn.pack(fill=tk.X, padx=5, pady=2)

            # Эффекты при наведении
            def on_enter(e, b=btn, k=screen_key):
                b.config(bg="#1abc9c")

            def on_leave(e, b=btn, k=screen_key):
                current = self.current_screen
                b.config(bg="#1abc9c" if k == current else "#34495e")

            btn.bind("<Enter>", on_enter)
            btn.bind("<Leave>", on_leave)

    def switch_to_screen_direct(self, screen_name):
        """Прямое переключение между экранами"""
        if screen_name not in self.screens:
            messagebox.showerror("Ошибка", f"Экран '{screen_name}' не найден")
            return

        print(f"🔄 Переключаемся на экран: {screen_name}")

        # Сохраняем текущие виджеты
        if self.widgets:
            self.screens[self.current_screen] = self.widgets.copy()

        # Меняем экран
        self.current_screen = screen_name

        # Очищаем и загружаем новый экран
        self.display_current_screen()

        # ПЕРЕСОЗДАЕМ панель навигации (обновляем цвета кнопок)
        self.create_screen_navigation_panel()

        self.update_status(f"📱 Экран: {screen_name} ({len(self.widgets)} виджетов)")

    def display_current_screen(self):
        """Отображает текущий экран - ПОЛНАЯ ОЧИСТКА"""
        # Полная очистка
        self.canvas.delete("all")
        self.widgets.clear()
        self.selected_widgets.clear()

        if self.current_screen not in self.screens:
            return

        # Загружаем виджеты
        for wo in self.screens[self.current_screen]:
            nw = WidgetItem(wo.widget_type, wo.x, wo.y, wo.config.copy())
            nw.current_width = wo.current_width
            nw.current_height = wo.current_height
            nw.events = wo.events.copy()
            nw.visible = wo.visible
            nw.locked = wo.locked
            self.widgets.append(nw)
            self.render_widget(nw)

        # Рисуем сетку
        self.draw_grid()

        # Обновляем панели
        self.update_layer_panel()
        self.update_logic_panel()
        self._update_minimap()

        # Привязываем события
        self.bind_navigation_events()

    def create_registration_flow(self):
        """Создает готовый поток регистрации с 4 экранами"""
        # Очищаем ВСЁ
        self.screens = {}
        self.current_screen = "main"

        # Удаляем старую панель
        if hasattr(self, 'nav_panel') and self.nav_panel:
            self.nav_panel.destroy()
            self.nav_panel = None

        # ========== ЭКРАН 1: ВХОД ==========
        screen_login = []
        screen_login.append(WidgetItem("Label", 200, 30,
                                       {"text": "🔐 Добро пожаловать", "bg": "#2c3e50", "fg": "white",
                                        "font": "Arial 14 bold"}))
        screen_login.append(WidgetItem("Label", 100, 100, {"text": "Email:", "bg": "#f0f0f0"}))
        screen_login.append(WidgetItem("Entry", 200, 100, {"width": 25, "bg": "white"}))
        screen_login.append(WidgetItem("Label", 100, 150, {"text": "Пароль:", "bg": "#f0f0f0"}))
        screen_login.append(WidgetItem("Entry", 200, 150, {"width": 25, "bg": "white", "show": "*"}))

        login_btn = WidgetItem("Button", 150, 200, {"text": "Войти", "bg": "#27ae60", "fg": "white"})
        login_btn.events["<Button-1>"] = "show_message('Вход выполнен')"
        screen_login.append(login_btn)

        forgot_btn = WidgetItem("Button", 120, 240, {"text": "❓ Забыли пароль?", "bg": "#f0f0f0", "fg": "#2980b9"})
        forgot_btn.events["<Button-1>"] = "switch_screen('forgot_password')"
        screen_login.append(forgot_btn)

        reg_btn = WidgetItem("Button", 120, 270, {"text": "📝 Регистрация", "bg": "#f0f0f0", "fg": "#2980b9"})
        reg_btn.events["<Button-1>"] = "switch_screen('register')"
        screen_login.append(reg_btn)

        # ========== ЭКРАН 2: ЗАБЫЛИ ПАРОЛЬ ==========
        screen_forgot = []
        screen_forgot.append(WidgetItem("Label", 180, 30,
                                        {"text": "🔐 Восстановление пароля", "bg": "#2c3e50", "fg": "white",
                                         "font": "Arial 12 bold"}))
        screen_forgot.append(WidgetItem("Label", 100, 100, {"text": "Ваш Email:", "bg": "#f0f0f0"}))
        screen_forgot.append(WidgetItem("Entry", 220, 100, {"width": 25, "bg": "white"}))
        screen_forgot.append(
            WidgetItem("Button", 180, 160, {"text": "📧 Отправить код", "bg": "#3498db", "fg": "white"}))

        back1 = WidgetItem("Button", 180, 200, {"text": "◀ Назад", "bg": "#95a5a6", "fg": "white"})
        back1.events["<Button-1>"] = "switch_screen('login')"
        screen_forgot.append(back1)

        # ========== ЭКРАН 3: ПОДТВЕРЖДЕНИЕ ==========
        screen_verify = []
        screen_verify.append(WidgetItem("Label", 180, 30,
                                        {"text": "📧 Подтверждение почты", "bg": "#2c3e50", "fg": "white",
                                         "font": "Arial 12 bold"}))
        screen_verify.append(WidgetItem("Label", 100, 120, {"text": "Код из письма:", "bg": "#f0f0f0"}))
        screen_verify.append(WidgetItem("Entry", 220, 120, {"width": 15, "bg": "white"}))
        screen_verify.append(WidgetItem("Button", 180, 180, {"text": "✅ Подтвердить", "bg": "#27ae60", "fg": "white"}))

        # ========== ЭКРАН 4: РЕГИСТРАЦИЯ ==========
        screen_register = []
        screen_register.append(WidgetItem("Label", 200, 30,
                                          {"text": "📝 Регистрация", "bg": "#2c3e50", "fg": "white",
                                           "font": "Arial 12 bold"}))

        fields = [("Имя:", 80), ("Email:", 130), ("Пароль:", 180), ("Подтверждение:", 230)]
        for label_text, y in fields:
            screen_register.append(WidgetItem("Label", 100, y, {"text": label_text, "bg": "#f0f0f0"}))
            entry_cfg = {"width": 25, "bg": "white"}
            if "Пароль" in label_text:
                entry_cfg["show"] = "*"
            screen_register.append(WidgetItem("Entry", 220, y, entry_cfg))

        screen_register.append(
            WidgetItem("Button", 150, 290, {"text": "📝 Зарегистрироваться", "bg": "#27ae60", "fg": "white"}))

        back2 = WidgetItem("Button", 150, 330, {"text": "◀ Назад", "bg": "#95a5a6", "fg": "white"})
        back2.events["<Button-1>"] = "switch_screen('login')"
        screen_register.append(back2)

        # Сохраняем экраны
        self.screens = {
            "login": screen_login,
            "forgot_password": screen_forgot,
            "verify_email": screen_verify,
            "register": screen_register
        }

        self.current_screen = "login"

        # СОЗДАЕМ ПАНЕЛЬ ТОЛЬКО ОДИН РАЗ
        self.create_screen_navigation_panel()

        # Отображаем первый экран
        self.display_current_screen()

        messagebox.showinfo("Успех", "Создано 4 экрана!\nИспользуйте панель '📱 ЭКРАНЫ' справа для переключения.")
        self.update_status("✓ Создано 4 экрана с навигацией!")

    def create_order_form(self):
        """Создает форму заказа"""
        # Очищаем старую панель
        if hasattr(self, 'nav_panel') and self.nav_panel:
            self.nav_panel.destroy()
            self.nav_panel = None

        widgets = []
        y = 50
        fields = ["Товар:", "Количество:", "Цена:", "Адрес доставки:", "Телефон:"]
        for field in fields:
            widgets.append(WidgetItem("Label", 80, y, {"text": field, "bg": "#f0f0f0"}))
            widgets.append(WidgetItem("Entry", 200, y, {"width": 30, "bg": "white"}))
            y += 40

        widgets.append(WidgetItem("Button", 150, y + 20, {"text": "🛒 Оформить заказ", "bg": "#27ae60", "fg": "white"}))
        widgets.append(WidgetItem("Button", 150, y + 60, {"text": "❌ Отмена", "bg": "#e74c3c", "fg": "white"}))

        self.screens["order_form"] = widgets
        self.current_screen = "order_form"

        # Используем ЕДИНЫЙ метод
        self.create_screen_navigation_panel()
        self.display_current_screen()

        self.update_status("✓ Создана форма заказа")

    def create_chat_interface(self):
        """Создает интерфейс чата"""
        if hasattr(self, 'nav_panel') and self.nav_panel:
            self.nav_panel.destroy()
            self.nav_panel = None

        widgets = []
        widgets.append(WidgetItem("Label", 100, 30,
                                  {"text": "💬 Чат", "bg": "#2c3e50", "fg": "white", "font": "Arial 14 bold"}))
        widgets.append(WidgetItem("Text", 80, 70, {"width": 50, "height": 15, "bg": "#f5f5f5"}))
        widgets.append(WidgetItem("Entry", 80, 320, {"width": 40, "bg": "white"}))
        widgets.append(WidgetItem("Button", 420, 318, {"text": "📤 Отправить", "bg": "#3498db", "fg": "white"}))

        self.screens["chat"] = widgets
        self.current_screen = "chat"

        self.create_screen_navigation_panel()
        self.display_current_screen()

        self.update_status("✓ Создан чат интерфейс")

    def create_dashboard(self):
        """Создает панель управления"""
        if hasattr(self, 'nav_panel') and self.nav_panel:
            self.nav_panel.destroy()
            self.nav_panel = None

        widgets = []
        widgets.append(WidgetItem("Label", 100, 30,
                                  {"text": "📊 Панель управления", "bg": "#2c3e50", "fg": "white",
                                   "font": "Arial 14 bold"}))
        widgets.append(WidgetItem("Frame", 80, 80, {"bg": "#ecf0f1", "width": 200, "height": 100}))
        widgets.append(WidgetItem("Label", 120, 120, {"text": "Пользователей: 1,234", "bg": "#ecf0f1"}))
        widgets.append(WidgetItem("Frame", 300, 80, {"bg": "#ecf0f1", "width": 200, "height": 100}))
        widgets.append(WidgetItem("Label", 340, 120, {"text": "Продаж: $12,345", "bg": "#ecf0f1"}))
        widgets.append(WidgetItem("Progressbar", 80, 210, {"value": 65, "length": 420, "mode": "determinate"}))
        widgets.append(WidgetItem("Label", 80, 240, {"text": "Прогресс: 65%", "bg": "white"}))

        self.screens["dashboard"] = widgets
        self.current_screen = "dashboard"

        self.create_screen_navigation_panel()
        self.display_current_screen()

        self.update_status("✓ Создана панель управления")

    def clear_all_screens(self):
        """Очищает все экраны и панель"""
        self.screens = {}
        self.current_screen = "main"

        # Удаляем панель
        if hasattr(self, 'nav_panel') and self.nav_panel:
            self.nav_panel.destroy()
            self.nav_panel = None

        if hasattr(self, 'screen_panel') and self.screen_panel:
            self.screen_panel.destroy()
            self.screen_panel = None

        self.canvas.delete("all")
        self.widgets.clear()
        self.selected_widgets.clear()
        self.draw_grid()
        self.update_status("Все экраны очищены")

    def create_screen_navigation_panel(self):
        """Создает панель с кнопками переключения экранов - БЕЗ НАЛОЖЕНИЯ"""

        # Удаляем старую панель полностью если она есть
        if hasattr(self, 'nav_panel') and self.nav_panel:
            self.nav_panel.destroy()

        # Создаем全新的 панель
        self.nav_panel = tk.Frame(self.root, bg="#2c3e50", relief=tk.RAISED, bd=2)
        self.nav_panel.place(relx=1.0, x=-10, y=50, anchor="ne")

        # Заголовок
        title_label = tk.Label(self.nav_panel, text="📱 ЭКРАНЫ", bg="#2c3e50", fg="white",
                               font=("Arial", 9, "bold"))
        title_label.pack(padx=10, pady=5, fill=tk.X)

        # Разделитель
        sep = tk.Frame(self.nav_panel, bg="#1abc9c", height=2)
        sep.pack(fill=tk.X, padx=5, pady=2)

        # Кнопки для каждого экрана
        names = {
            "login": "🔐 Вход",
            "forgot_password": "❓ Забыли пароль",
            "verify_email": "📧 Подтверждение",
            "register": "📝 Регистрация",
            "order_form": "🛒 Заказ",
            "chat": "💬 Чат",
            "dashboard": "📊 Дашборд",
            "main": "🏠 Главный"
        }

        for screen_key in self.screens.keys():
            btn_text = names.get(screen_key, f"📄 {screen_key}")

            btn = tk.Button(
                self.nav_panel,
                text=btn_text,
                bg="#1abc9c" if screen_key == self.current_screen else "#34495e",
                fg="white",
                relief=tk.FLAT,
                cursor="hand2",
                font=("Arial", 8),
                command=lambda k=screen_key: self.switch_to_screen_direct(k)
            )
            btn.pack(fill=tk.X, padx=5, pady=2)

            # Эффекты при наведении
            def on_enter(e, b=btn, k=screen_key):
                b.config(bg="#1abc9c")

            def on_leave(e, b=btn, k=screen_key):
                b.config(bg="#1abc9c" if k == self.current_screen else "#34495e")

            btn.bind("<Enter>", on_enter)
            btn.bind("<Leave>", on_leave)
    def refresh_current_screen(self):
        """Принудительно обновляет текущий экран"""
        if self.current_screen in self.screens:
            self.display_current_screen()

    def switch_to_screen_direct(self, screen_name):
        """Прямое переключение между экранами - ОБНОВЛЯЕТ КНОПКИ"""
        if screen_name not in self.screens:
            return

        print(f"Переключаемся на экран: {screen_name}")

        # Меняем текущий экран
        self.current_screen = screen_name

        # ПЕРЕСОЗДАЕМ панель заново (чтобы обновить цвета кнопок)
        self.create_screen_navigation_panel()

        # Полностью перерисовываем холст
        self.display_current_screen()

    def clear_all_screens(self):
        """Очищает все экраны и панель"""
        self.screens = {}
        self.current_screen = "main"

        if hasattr(self, 'nav_panel') and self.nav_panel:
            self.nav_panel.destroy()
            self.nav_panel = None

        self.canvas.delete("all")
        self.widgets.clear()
        self.selected_widgets.clear()
        self.draw_grid()
        self.update_status("Все экраны очищены")
    def display_current_screen(self):
        """Отображает текущий экран на холсте - ПОЛНОСТЬЮ ОЧИЩАЕТ перед показом"""

        # Полностью очищаем холст
        self.canvas.delete("all")
        self.widgets.clear()
        self.selected_widgets.clear()

        if self.current_screen not in self.screens:
            return

        # Создаем виджеты текущего экрана
        for wo in self.screens[self.current_screen]:
            nw = WidgetItem(wo.widget_type, wo.x, wo.y, wo.config.copy())
            nw.current_width = wo.current_width
            nw.current_height = wo.current_height
            nw.events = wo.events.copy()
            nw.visible = wo.visible
            nw.locked = wo.locked
            self.widgets.append(nw)
            self.render_widget(nw)

        # Рисуем сетку заново
        self.draw_grid()

        # Обновляем панели
        self.update_layer_panel()
        self.update_logic_panel()
        self._update_minimap()

        # Привязываем события для навигации
        self.bind_navigation_events()

        self.update_status(f"📱 Показан экран: {self.current_screen} ({len(self.widgets)} виджетов)")

    def bind_navigation_events(self):
        """Привязывает события для навигации между экранами"""
        for wo in self.widgets:
            if wo.events:
                for event, command in wo.events.items():
                    if command.startswith("switch_screen"):
                        # Извлекаем имя экрана
                        import re
                        match = re.search(r"['\"]([^'\"]+)['\"]", command)
                        if match:
                            screen_name = match.group(1)

                            # Находим реальный виджет на холсте
                            if wo.widget_instance and wo.frame:
                                for child in wo.frame.winfo_children():
                                    if hasattr(child, 'bind'):
                                        # Отвязываем старые события
                                        try:
                                            child.unbind(event)
                                        except:
                                            pass
                                        # Привязываем новое
                                        child.bind(event, lambda e, sn=screen_name: self.switch_to_screen_direct(sn))
                    elif command.startswith("show_message"):
                        import re
                        match = re.search(r"['\"]([^'\"]+)['\"]", command)
                        if match:
                            msg = match.group(1)
                            if wo.widget_instance and wo.frame:
                                for child in wo.frame.winfo_children():
                                    if hasattr(child, 'bind'):
                                        try:
                                            child.unbind(event)
                                        except:
                                            pass
                                        child.bind(event, lambda e, m=msg: messagebox.showinfo("Информация", m))

    def preview_with_screens(self):
        """Предпросмотр с экранами: полные виджеты, логика из вкладки «Логика», панель ИИ."""
        import re

        if not self.screens:
            messagebox.showinfo(
                "Предпросмотр",
                "Нет экранов — добавьте шаблон с экранами или сгенерируйте интерфейс через ИИ.",
            )
            return

        win = tk.Toplevel(self.root)
        win.title("👁 Предпросмотр + ИИ")
        win.geometry("920x760")
        win.configure(bg="#f0f0f0")

        screen_state = {"name": None}

        pw = ttk.PanedWindow(win, orient=tk.VERTICAL)
        pw.pack(fill=tk.BOTH, expand=True, padx=6, pady=6)

        upper = ttk.Frame(pw)
        pw.add(upper, weight=3)

        ttk.Label(
            upper,
            text="Предпросмотр экранов (как на холсте) + правила логики",
            font=("Arial", 12, "bold"),
        ).pack(anchor=tk.W, padx=8, pady=6)

        nav_frame = tk.Frame(upper, bg="#2c3e50")
        nav_frame.pack(fill=tk.X, padx=8, pady=2)

        tk.Label(
            nav_frame,
            text="📱 Экраны:",
            bg="#2c3e50",
            fg="white",
            font=("Arial", 9, "bold"),
        ).pack(side=tk.LEFT, padx=10)

        canvas_holder = tk.Frame(upper, bg="white")
        canvas_holder.pack(fill=tk.BOTH, expand=True, padx=8, pady=4)

        cv = tk.Canvas(
            canvas_holder,
            bg="white",
            highlightthickness=1,
            highlightbackground="#ccc",
        )
        sc = ttk.Scrollbar(canvas_holder, orient="vertical", command=cv.yview)
        cv.configure(yscrollcommand=sc.set)
        sc.pack(side=tk.RIGHT, fill=tk.Y)
        cv.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        def _inner_from_container(container):
            for ch in container.winfo_children():
                return ch
            return None

        def render_preview_screen(screen_name):
            screen_state["name"] = screen_name
            cv.delete("all")

            if screen_name not in self.screens:
                return

            preview_widgets = {}
            max_x, max_y = 400, 300

            for wo in self.screens[screen_name]:
                if not getattr(wo, "visible", True):
                    continue
                try:
                    w = self.create_preview_widget(cv, wo.widget_type, wo.config, wo)
                    cid = cv.create_window(wo.x, wo.y, window=w, anchor="nw")
                    preview_widgets[str(wo.id)] = {
                        "widget": w,
                        "canvas_id": cid,
                        "x": wo.x,
                        "y": wo.y,
                    }
                    max_x = max(max_x, wo.x + wo.current_width + 40)
                    max_y = max(max_y, wo.y + wo.current_height + 40)
                except Exception:
                    pass

            for wo in self.screens[screen_name]:
                if not getattr(wo, "visible", True):
                    continue
                wid = str(wo.id)
                pdata = preview_widgets.get(wid)
                if not pdata:
                    continue
                inner = _inner_from_container(pdata["widget"])
                if not inner:
                    continue
                for ev, command in wo.events.items():
                    if command.startswith("switch_screen"):
                        m = re.search(r"['\"]([^'\"]+)['\"]", command)
                        target = m.group(1) if m else ""
                        inner.bind(ev, lambda e, t=target: render_preview_screen(t))
                    elif command.startswith("show_message"):
                        m = re.search(r"['\"]([^'\"]+)['\"]", command)
                        msg = m.group(1) if m else ""
                        inner.bind(ev, lambda e, m=msg: messagebox.showinfo("Инфо", m))

            if self.logic_rules and preview_widgets:
                self.apply_logic_to_preview(preview_widgets, cv)

            cv.configure(scrollregion=(0, 0, max_x, max_y))

        screen_labels = {
            "login": "Вход",
            "register": "Регистрация",
            "forgot_password": "Забыли пароль",
            "verify_email": "Подтверждение",
            "main": "Главный",
        }

        for screen_key in self.screens.keys():
            lbl = screen_labels.get(screen_key, screen_key)
            btn = tk.Button(
                nav_frame,
                text=lbl,
                bg="#34495e",
                fg="white",
                command=lambda k=screen_key: render_preview_screen(k),
            )
            btn.pack(side=tk.LEFT, padx=2)
            btn.bind("<Enter>", lambda e, b=btn: b.config(bg="#1abc9c"))
            btn.bind("<Leave>", lambda e, b=btn: b.config(bg="#34495e"))

        tk.Button(
            nav_frame,
            text="✕ Закрыть",
            bg="#e74c3c",
            fg="white",
            command=win.destroy,
        ).pack(side=tk.RIGHT, padx=10)

        lower = ttk.Frame(pw)
        pw.add(lower, weight=1)
        self.attach_preview_ai_panel(win, screen_state, parent=lower)

        first = (
            self.current_screen
            if self.current_screen in self.screens
            else next(iter(self.screens.keys()))
        )
        render_preview_screen(first)
    def show_screens_list(self):
        """Показывает список всех экранов"""
        if not self.screens:
            messagebox.showinfo("Экраны", "Нет созданных экранов")
            return

        win = tk.Toplevel(self.root)
        win.title("📱 Список экранов")
        win.geometry("300x400")

        ttk.Label(win, text="Доступные экраны:", font=("Arial", 10, "bold")).pack(pady=10)

        listbox = tk.Listbox(win)
        listbox.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)

        for name in self.screens.keys():
            count = len(self.screens[name])
            listbox.insert(tk.END, f"{name} ({count} виджетов)")
            if name == self.current_screen:
                listbox.itemconfig(tk.END, bg="#d4efdf")

        def switch():
            if listbox.curselection():
                name = list(listbox.keys())[listbox.curselection()[0]]
                self.switch_to_screen(name)
                win.destroy()

        ttk.Button(win, text="Переключиться", command=switch).pack(pady=10)
    # ── SETUP ─────────────────────────────────────────────────────────────────
    def setup_ui(self):
        # Top toolbar
        top = ttk.Frame(self.root)
        top.pack(fill=tk.X, padx=10, pady=4)

        for txt, cmd in [("💾 Сохранить", self.save_project),
                         ("📂 Открыть", self.load_project),
                         ("🐍 Код", self.generate_code),
                         ("▶ Предпросмотр", self.preview)]:
            ttk.Button(top, text=txt, command=cmd).pack(side=tk.LEFT, padx=2)

        ttk.Separator(top, orient="vertical").pack(side=tk.LEFT, padx=6, fill=tk.Y)
        ttk.Button(top, text="🔑 API", command=self._set_api_key).pack(side=tk.LEFT, padx=2)
        ttk.Button(top, text="🤖 ИИ: макет", command=self.open_ai_generate_dialog).pack(side=tk.LEFT, padx=2)
        ttk.Button(top, text="🤖 ИИ: экраны", command=self.open_ai_multi_screen_dialog).pack(side=tk.LEFT, padx=2)

        ttk.Separator(top, orient="vertical").pack(side=tk.LEFT, padx=6, fill=tk.Y)
        ttk.Button(top, text="↩ Отмена", command=self.undo_manager.undo).pack(side=tk.LEFT, padx=2)
        ttk.Button(top, text="↪ Повтор", command=self.undo_manager.redo).pack(side=tk.LEFT, padx=2)

        ttk.Separator(top, orient="vertical").pack(side=tk.LEFT, padx=6, fill=tk.Y)
        ttk.Button(top, text="🔍+", command=self.zoom_in).pack(side=tk.LEFT, padx=2)
        ttk.Button(top, text="🔍-", command=self.zoom_out).pack(side=tk.LEFT, padx=2)
        ttk.Button(top, text="✋ Панорама", command=self.toggle_pan_mode).pack(side=tk.LEFT, padx=2)

        ttk.Separator(top, orient="vertical").pack(side=tk.LEFT, padx=6, fill=tk.Y)
        ttk.Button(top, text="📦 Группировать", command=self.group_selected).pack(side=tk.LEFT, padx=2)
        ttk.Button(top, text="📤 Разгруппировать", command=self.ungroup_selected).pack(side=tk.LEFT, padx=2)
        ttk.Button(top, text="🗑 Направляющие", command=self.clear_guides).pack(side=tk.LEFT, padx=2)

        self.snap_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(top, text="Сетка", variable=self.snap_var,
                        command=self.toggle_grid).pack(side=tk.RIGHT, padx=6)
        self.status_label = ttk.Label(top, text="Готов", foreground="gray")
        self.status_label.pack(side=tk.RIGHT, padx=10)

        # Main paned
        main = ttk.PanedWindow(self.root, orient=tk.HORIZONTAL)
        main.pack(fill=tk.BOTH, expand=True, padx=10, pady=4)

        # LEFT — вся панель (виджеты, шаблоны, быстрые решения, экраны) в одной вертикальной прокрутке
        tool_frame = ttk.LabelFrame(main, text="🧰 Инструменты", padding=2)
        self.tool_frame = tool_frame
        main.add(tool_frame, weight=1)

        tb_wrap = tk.Frame(tool_frame)
        tb_wrap.pack(fill=tk.BOTH, expand=True)

        self.toolbar_scroll = tk.Scrollbar(
            tb_wrap,
            orient=tk.VERTICAL,
            width=14,
            bg="#d0d0d0",
            troughcolor="#ececec",
        )
        self.toolbar_scroll.pack(side=tk.RIGHT, fill=tk.Y)

        self.toolbar_canvas = tk.Canvas(
            tb_wrap,
            highlightthickness=0,
            bg="#f0f0f0",
        )
        self.toolbar_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.toolbar_canvas.configure(yscrollcommand=self.toolbar_scroll.set)
        self.toolbar_scroll.config(command=self.toolbar_canvas.yview)

        self.toolbar_inner = ttk.Frame(self.toolbar_canvas)
        self._toolbar_inner_win = self.toolbar_canvas.create_window(
            (0, 0),
            window=self.toolbar_inner,
            anchor=tk.NW,
        )

        def _toolbar_inner_cfg(_event=None):
            bb = self.toolbar_canvas.bbox("all")
            if bb:
                self.toolbar_canvas.configure(scrollregion=bb)

        def _toolbar_canvas_cfg(event):
            try:
                self.toolbar_canvas.itemconfigure(self._toolbar_inner_win, width=event.width)
            except tk.TclError:
                pass
            _toolbar_inner_cfg()

        self.toolbar_inner.bind("<Configure>", _toolbar_inner_cfg)
        self.toolbar_canvas.bind("<Configure>", _toolbar_canvas_cfg)

        def _toolbar_wheel(event):
            if not self._pointer_over_toolbar(event):
                return
            if event.delta:
                self.toolbar_canvas.yview_scroll(int(-event.delta / 120), "units")

        def _toolbar_wheel_linux_up(_e):
            if self._pointer_over_toolbar(_e):
                self.toolbar_canvas.yview_scroll(-3, "units")

        def _toolbar_wheel_linux_dn(_e):
            if self._pointer_over_toolbar(_e):
                self.toolbar_canvas.yview_scroll(3, "units")

        self.root.bind_all("<MouseWheel>", _toolbar_wheel, add="+")
        self.root.bind_all("<Button-4>", _toolbar_wheel_linux_up, add="+")
        self.root.bind_all("<Button-5>", _toolbar_wheel_linux_dn, add="+")

        self.search_var = tk.StringVar()
        se = ttk.Entry(self.toolbar_inner, textvariable=self.search_var)
        se.pack(fill=tk.X, pady=(4, 4), padx=4)
        se.bind("<KeyRelease>", lambda e: self._rebuild_palette())

        self.palette_frame = ttk.Frame(self.toolbar_inner)
        self.palette_frame.pack(fill=tk.X, padx=4, pady=(0, 4))

        self.widget_buttons = {}
        self._rebuild_palette()

        ttk.Separator(self.toolbar_inner, orient="horizontal").pack(fill=tk.X, pady=7, padx=4)
        ttk.Label(self.toolbar_inner, text="📦 Шаблоны форм", font=("Arial", 9, "bold")).pack(anchor=tk.W, padx=4)
        self.template_listbox = tk.Listbox(self.toolbar_inner, height=4)
        self.template_listbox.pack(fill=tk.X, pady=2, padx=4)
        self.template_listbox.bind("<Double-Button-1>", self.insert_template)

        for t in ["Форма входа", "Форма регистрации", "Dashboard", "Калькулятор", "Анкета пользователя"]:
            self.template_listbox.insert(tk.END, t)

        ttk.Separator(self.toolbar_inner, orient="horizontal").pack(fill=tk.X, pady=7, padx=4)

        quick_frame = ttk.LabelFrame(self.toolbar_inner, text="🚀 Быстрые решения", padding=5)
        quick_frame.pack(fill=tk.X, pady=5, padx=4)

        ttk.Button(quick_frame, text="📱 Форма регистрации (4 экрана)",
                   command=self.create_registration_flow).pack(fill=tk.X, pady=2)

        ttk.Button(quick_frame, text="🛒 Форма заказа",
                   command=self.create_order_form).pack(fill=tk.X, pady=2)

        ttk.Button(quick_frame, text="💬 Чат интерфейс",
                   command=self.create_chat_interface).pack(fill=tk.X, pady=2)

        ttk.Button(quick_frame, text="📊 Панель управления",
                   command=self.create_dashboard).pack(fill=tk.X, pady=2)

        ttk.Separator(self.toolbar_inner, orient="horizontal").pack(fill=tk.X, pady=7, padx=4)

        screen_frame = ttk.LabelFrame(self.toolbar_inner, text="📱 Управление экранами", padding=5)
        screen_frame.pack(fill=tk.X, pady=(5, 8), padx=4)
        ttk.Button(screen_frame, text="➕ Новый экран", command=self.add_new_screen).pack(fill=tk.X, pady=1)
        ttk.Button(screen_frame, text="🗑 Удалить экран", command=self.delete_current_screen).pack(fill=tk.X, pady=1)
        ttk.Button(screen_frame, text="📋 Список экранов", command=self.show_screens_list).pack(fill=tk.X, pady=1)

        self.toolbar_inner.update_idletasks()
        _bb = self.toolbar_canvas.bbox("all")
        if _bb:
            self.toolbar_canvas.configure(scrollregion=_bb)

        # CENTER — canvas with rulers
        canvas_outer = ttk.LabelFrame(main, text="🎨 Рабочая область", padding=2)
        main.add(canvas_outer, weight=5)

        canvas_outer.columnconfigure(1, weight=1)
        canvas_outer.rowconfigure(1, weight=1)

        corner = tk.Frame(canvas_outer, bg="#e0e0e0", width=20, height=20)
        corner.grid(row=0, column=0, sticky="nsew")

        ruler_h_host = tk.Frame(canvas_outer, bg="#f0f0f0", height=20)
        ruler_h_host.grid(row=0, column=1, sticky="ew")
        self.ruler_h = tk.Canvas(ruler_h_host, height=20, bg="#f0f0f0", highlightthickness=0)
        self.ruler_h.pack(fill=tk.X, expand=True)

        ruler_v_host = tk.Frame(canvas_outer, bg="#f0f0f0", width=20)
        ruler_v_host.grid(row=1, column=0, sticky="ns")
        self.ruler_v = tk.Canvas(ruler_v_host, width=20, bg="#f0f0f0", highlightthickness=0)
        self.ruler_v.pack(fill=tk.Y, expand=True)

        canvas_host = tk.Frame(canvas_outer)
        canvas_host.grid(row=1, column=1, sticky="nsew")

        self.canvas = tk.Canvas(canvas_host, bg="white", highlightthickness=0)
        self.canvas.grid(row=0, column=0, sticky="nsew")

        # tk.Scrollbar — заметнее, чем ttk в теме clam
        self.canvas_vscroll = tk.Scrollbar(
            canvas_host,
            orient=tk.VERTICAL,
            command=self.canvas.yview,
            width=16,
            bg="#c8c8c8",
            troughcolor="#ececec",
            activebackground="#a0a0a0",
        )
        self.canvas_vscroll.grid(row=0, column=1, sticky="ns")

        self.canvas_hscroll = tk.Scrollbar(
            canvas_host,
            orient=tk.HORIZONTAL,
            command=self.canvas.xview,
            width=16,
            bg="#c8c8c8",
            troughcolor="#ececec",
            activebackground="#a0a0a0",
        )
        self.canvas_hscroll.grid(row=1, column=0, sticky="ew")

        canvas_host.grid_columnconfigure(0, weight=1, minsize=50)
        canvas_host.grid_columnconfigure(1, weight=0, minsize=18)
        canvas_host.grid_rowconfigure(0, weight=1, minsize=50)
        canvas_host.grid_rowconfigure(1, weight=0, minsize=18)

        sb_corner = tk.Frame(canvas_host, width=18, height=18, bg="#e8e8e8")
        sb_corner.grid(row=1, column=1, sticky="nsew")

        def _yscroll(*args):
            self.canvas_vscroll.set(*args)
            self.root.after_idle(self._draw_rulers)

        def _xscroll(*args):
            self.canvas_hscroll.set(*args)
            self.root.after_idle(self._draw_rulers)

        self.canvas.configure(yscrollcommand=_yscroll, xscrollcommand=_xscroll)

        self.mode_label = ttk.Label(canvas_outer, text="Режим: Перемещение", foreground="blue")
        self.mode_label.grid(row=2, column=0, columnspan=2, sticky="w", padx=4, pady=2)

        self.draw_grid()

        # Ruler guide bindings
        self.ruler_h.bind("<ButtonPress-1>", self._rh_press)
        self.ruler_h.bind("<B1-Motion>", self._rh_drag)
        self.ruler_h.bind("<ButtonRelease-1>", self._rh_release)
        self.ruler_v.bind("<ButtonPress-1>", self._rv_press)
        self.ruler_v.bind("<B1-Motion>", self._rv_drag)
        self.ruler_v.bind("<ButtonRelease-1>", self._rv_release)

        # Canvas bindings
        self.canvas.bind("<ButtonPress-1>", self.on_canvas_press)
        self.canvas.bind("<B1-Motion>", self.on_canvas_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_canvas_release)
        self.canvas.bind("<Double-Button-1>", self.on_canvas_double_click)
        self.canvas.bind("<Button-3>", self.show_context_menu)
        self.canvas.bind("<MouseWheel>", self.on_mouse_wheel)
        self.canvas.bind("<ButtonPress-2>", self.on_pan_start)
        self.canvas.bind("<B2-Motion>", self.on_pan_drag)
        self.canvas.bind("<ButtonRelease-2>", self.on_pan_release)
        self.canvas.bind("<Configure>", lambda e: self.root.after(50, self._draw_rulers))
        self.canvas.bind("<Motion>", self._canvas_motion)

        # RIGHT — notebook
        right_nb = ttk.Notebook(main)
        main.add(right_nb, weight=1)

        # ========== ВКЛАДКА СЛОЁВ ==========
        lay_tab = ttk.Frame(right_nb)
        right_nb.add(lay_tab, text="🗂 Слои")

        lc = ttk.Frame(lay_tab)
        lc.pack(fill=tk.X, pady=2)
        ttk.Button(lc, text="▲", width=3, command=self.move_layer_up).pack(side=tk.LEFT, padx=1)
        ttk.Button(lc, text="▼", width=3, command=self.move_layer_down).pack(side=tk.LEFT, padx=1)
        ttk.Button(lc, text="👁 Вкл/Выкл", command=self._toggle_vis_sel).pack(side=tk.LEFT, padx=2)
        ttk.Button(lc, text="🔒 Лок", command=self._toggle_lock_sel).pack(side=tk.LEFT, padx=1)

        lyr_cv = tk.Canvas(lay_tab, highlightthickness=0, bg="white")
        lyr_sc = ttk.Scrollbar(lay_tab, orient="vertical", command=lyr_cv.yview)
        lyr_sc.pack(side=tk.RIGHT, fill=tk.Y)
        lyr_cv.pack(fill=tk.BOTH, expand=True)
        lyr_cv.configure(yscrollcommand=lyr_sc.set)

        self.layer_inner = tk.Frame(lyr_cv, bg="white")
        lyr_cv.create_window(0, 0, anchor="nw", window=self.layer_inner)
        self.layer_inner.bind("<Configure>", lambda e: lyr_cv.configure(scrollregion=lyr_cv.bbox("all")))

        # ========== ВКЛАДКА СВОЙСТВ ==========
        self.prop_tab = ttk.Frame(right_nb)
        right_nb.add(self.prop_tab, text="⚙ Свойства")

        prop_canvas = tk.Canvas(self.prop_tab, highlightthickness=0)
        prop_scroll = ttk.Scrollbar(self.prop_tab, orient="vertical", command=prop_canvas.yview)
        prop_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        prop_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        prop_canvas.configure(yscrollcommand=prop_scroll.set)

        self.prop_inner = ttk.Frame(prop_canvas)
        prop_canvas.create_window(0, 0, anchor="nw", window=self.prop_inner)
        self.prop_inner.bind("<Configure>", lambda e: prop_canvas.configure(scrollregion=prop_canvas.bbox("all")))
        self.prop_widgets = {}

        # ========== ВКЛАДКА ЛОГИКА ==========
        logic_tab = ttk.Frame(right_nb)
        right_nb.add(logic_tab, text="🧠 Логика")

        logic_top = ttk.Frame(logic_tab)
        logic_top.pack(fill=tk.X, padx=5, pady=5)

        ttk.Label(logic_top, text="Выбранный виджет:").pack(side=tk.LEFT)
        self.logic_widget_var = tk.StringVar(value="Ничего не выбрано")
        self.logic_widget_label = ttk.Label(logic_top, textvariable=self.logic_widget_var,
                                            foreground="blue", font=("Arial", 9, "bold"))
        self.logic_widget_label.pack(side=tk.LEFT, padx=5)

        btn_frame = ttk.Frame(logic_top)
        btn_frame.pack(side=tk.RIGHT)
        ttk.Button(btn_frame, text="📋 Шаблоны", command=self.show_logic_templates).pack(side=tk.LEFT, padx=2)
        ttk.Button(btn_frame, text="➕ Добавить", command=self.add_logic_rule).pack(side=tk.LEFT, padx=2)
        ttk.Button(btn_frame, text="🗑 Очистить", command=self.clear_all_rules).pack(side=tk.LEFT, padx=2)

        logic_canvas_frame = ttk.Frame(logic_tab)
        logic_canvas_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        self.logic_canvas = tk.Canvas(logic_canvas_frame, bg="#f5f5f5", highlightthickness=1,
                                      highlightbackground="#ccc")
        logic_scroll_y = ttk.Scrollbar(logic_canvas_frame, orient="vertical", command=self.logic_canvas.yview)
        logic_scroll_x = ttk.Scrollbar(logic_canvas_frame, orient="horizontal", command=self.logic_canvas.xview)
        self.logic_canvas.configure(yscrollcommand=logic_scroll_y.set, xscrollcommand=logic_scroll_x.set)

        logic_scroll_y.pack(side=tk.RIGHT, fill=tk.Y)
        logic_scroll_x.pack(side=tk.BOTTOM, fill=tk.X)
        self.logic_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        self.logic_inner = tk.Frame(self.logic_canvas, bg="#f5f5f5")
        self.logic_canvas.create_window(0, 0, anchor="nw", window=self.logic_inner)
        self.logic_inner.bind("<Configure>",
                              lambda e: self.logic_canvas.configure(scrollregion=self.logic_canvas.bbox("all")))

        logic_bottom = ttk.Frame(logic_tab)
        logic_bottom.pack(fill=tk.X, padx=5, pady=5)
        ttk.Button(logic_bottom, text="▶ Тестировать", command=self.test_logic).pack(side=tk.LEFT, padx=2)
        ttk.Button(logic_bottom, text="💾 Сохранить логику", command=self.save_logic).pack(side=tk.LEFT, padx=2)
        ttk.Button(logic_bottom, text="📋 Код", command=self.generate_logic_code).pack(side=tk.LEFT, padx=2)
        self.logic_status = ttk.Label(logic_bottom, text="", foreground="green")
        self.logic_status.pack(side=tk.LEFT, padx=10)

        # ========== ВКЛАДКА СОБЫТИЙ ==========
        ev_tab = ttk.Frame(right_nb)
        right_nb.add(ev_tab, text="⚡ События")

        self.event_widgets = {}
        events_frame = ttk.LabelFrame(ev_tab, text="Привязка событий", padding=5)
        events_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        events = ["<Button-1>", "<Double-Button-1>", "<Enter>", "<Leave>", "<Key>", "<Return>", "<Escape>"]
        for i, ev in enumerate(events):
            ttk.Label(events_frame, text=ev, width=15).grid(row=i, column=0, sticky=tk.W, pady=3)
            ent = ttk.Entry(events_frame, width=25)
            ent.grid(row=i, column=1, sticky=tk.EW, pady=3, padx=(5, 0))
            ttk.Button(events_frame, text="📝", width=3,
                       command=lambda e=ev, w=ent: self.edit_event_code(e, w)).grid(row=i, column=2, padx=2)
            self.event_widgets[ev] = ent
        events_frame.columnconfigure(1, weight=1)

        # ========== ВКЛАДКА ИСТОРИИ ==========
        hist_tab = ttk.Frame(right_nb)
        right_nb.add(hist_tab, text="📜 История")

        ttk.Label(hist_tab, text="Последние действия:", font=("Arial", 9, "bold")).pack(anchor=tk.W, padx=5, pady=3)
        hcv = tk.Canvas(hist_tab, highlightthickness=0, bg="white")
        hsc = ttk.Scrollbar(hist_tab, orient="vertical", command=hcv.yview)
        hsc.pack(side=tk.RIGHT, fill=tk.Y)
        hcv.pack(fill=tk.BOTH, expand=True)
        hcv.configure(yscrollcommand=hsc.set)
        self.history_inner = tk.Frame(hcv, bg="white")
        hcv.create_window(0, 0, anchor="nw", window=self.history_inner)
        self.history_inner.bind("<Configure>", lambda e: hcv.configure(scrollregion=hcv.bbox("all")))

        # Context menu
        self.ctx = tk.Menu(self.root, tearoff=0)
        self.ctx.add_command(label="✂ Вырезать", command=self.cut_selection)
        self.ctx.add_command(label="📋 Копировать", command=self.copy_selection)
        self.ctx.add_command(label="📌 Вставить", command=self.paste_selection)
        self.ctx.add_command(label="📄 Дублировать", command=self._duplicate)
        self.ctx.add_separator()
        self.ctx.add_command(label="🗑 Удалить", command=self.delete_selected)
        self.ctx.add_command(label="📤 На перед", command=self.bring_to_front)
        self.ctx.add_command(label="📥 На зад", command=self.send_to_back)

        # Инициализация атрибутов
        self.screens = {}
        self.current_screen = "main"
        self.screen_transitions = []
        self.logic_rules = {}
        self.current_logic_widget = None
    def show_logic_templates(self):
        """Показывает окно с готовыми шаблонами логики"""
        if not self.current_logic_widget:
            messagebox.showwarning("Внимание", "Сначала выберите виджет на холсте!")
            return

        win = tk.Toplevel(self.root)
        win.title("📋 Готовые шаблоны логики")
        win.geometry("600x500")
        win.transient(self.root)

        ttk.Label(win, text="Выберите шаблон для виджета:", font=("Arial", 12, "bold")).pack(pady=10)

        # Создаем фрейм с прокруткой
        canvas = tk.Canvas(win, highlightthickness=0)
        scrollbar = ttk.Scrollbar(win, orient="vertical", command=canvas.yview)
        scrollable_frame = ttk.Frame(canvas)

        scrollable_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)

        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        # Шаблоны логики
        templates = [
            {
                "name": "🔘 Кнопка меняет текст на Label",
                "desc": "При нажатии на кнопку текст Label меняется",
                "rules": [
                    {"event": "click", "action": "set_text", "target": "", "value": "Привет!"}
                ]
            },
            {
                "name": "🎨 Смена цвета при наведении",
                "desc": "При наведении мыши фон меняется, при уходе возвращается",
                "rules": [
                    {"event": "enter", "action": "set_bg", "target": "", "value": "#ffcccc"},
                    {"event": "leave", "action": "set_bg", "target": "", "value": "#e0e0e0"}
                ]
            },
            {
                "name": "👁 Показать/скрыть другой виджет",
                "desc": "По клику скрывает/показывает целевой виджет",
                "rules": [
                    {"event": "click", "action": "show_hide", "target": "", "value": "toggle"}
                ]
            },
            {
                "name": "📝 Копировать текст из Entry в Label",
                "desc": "При вводе текста в Entry, Label обновляется",
                "rules": [
                    {"event": "key_press", "action": "set_text", "target": "", "value": ""}
                ]
            },
            {
                "name": "🎚️ Ползунок меняет значение прогресс-бара",
                "desc": "При движении ползунка обновляет прогресс-бар",
                "rules": [
                    {"event": "click", "action": "set_value", "target": "", "value": ""}
                ]
            },
            {
                "name": "✅ Вкл/Выкл кнопку через чекбокс",
                "desc": "Чекбокс включает/выключает кнопку",
                "rules": [
                    {"event": "click", "action": "enable_disable", "target": "", "value": "toggle"}
                ]
            },
            {
                "name": "🔄 Двойной клик для сброса",
                "desc": "Двойной клик сбрасывает текст на значение по умолчанию",
                "rules": [
                    {"event": "double_click", "action": "set_text", "target": "", "value": "По умолчанию"}
                ]
            },
            {
                "name": "🎯 Комбо: клик + смена цвета + текст",
                "desc": "При клике меняется и текст и цвет",
                "rules": [
                    {"event": "click", "action": "set_text", "target": "", "value": "Нажато!"},
                    {"event": "click", "action": "set_bg", "target": "", "value": "#90ee90"}
                ]
            },
            {
                "name": "🔐 Регистрация: если два поля совпадают",
                "desc": "Действие только если значения двух виджетов (например пароль и подтверждение) равны — выберите поле A и B",
                "rules": [
                    {"event": "click", "action": "set_text", "target": "", "value": "Пароли совпадают",
                     "condition": "if_equal", "compare_a": "", "compare_b": ""}
                ]
            },
            {
                "name": "⚠️ Если поля не совпадают",
                "desc": "Действие только если значения двух полей различаются (показать ошибку)",
                "rules": [
                    {"event": "click", "action": "set_text", "target": "", "value": "Ошибка: не совпадают",
                     "condition": "if_not_equal", "compare_a": "", "compare_b": ""}
                ]
            }
        ]

        for template in templates:
            frame = tk.Frame(scrollable_frame, bg="white", relief=tk.RAISED, bd=1)
            frame.pack(fill=tk.X, padx=10, pady=5)

            # Заголовок
            tk.Label(frame, text=template["name"], bg="white", font=("Arial", 10, "bold"),
                     anchor=tk.W).pack(fill=tk.X, padx=10, pady=(5, 0))

            # Описание
            tk.Label(frame, text=template["desc"], bg="white", fg="gray", font=("Arial", 8),
                     anchor=tk.W).pack(fill=tk.X, padx=10, pady=(0, 5))

            # Предпросмотр правил
            rules_text = " → ".join([f"{r['event']} -> {r['action']}" for r in template["rules"]])
            tk.Label(frame, text=rules_text, bg="#f0f0f0", fg="#555", font=("Consolas", 7),
                     anchor=tk.W).pack(fill=tk.X, padx=10, pady=5)

            # Кнопка применения
            def apply_template(t=template):
                self.apply_logic_template(t["rules"])
                win.destroy()
                self.logic_status.config(text=f"✓ Применен шаблон: {t['name']}", foreground="green")
                self.root.after(3000, lambda: self.logic_status.config(text=""))

            ttk.Button(frame, text="✅ Применить", command=apply_template).pack(anchor=tk.E, padx=10, pady=5)

    def apply_logic_template(self, rules):
        """Применяет шаблон логики к выбранному виджету"""
        if not self.current_logic_widget:
            return

        # Очищаем старые правила если нужно
        if messagebox.askyesno("Шаблон", "Очистить существующие правила для этого виджета?"):
            self.logic_rules[self.current_logic_widget] = []

        # Добавляем новые правила
        for rule in rules:
            new_rule = rule.copy()

            # Если цель не указана, нужно выбрать
            if not new_rule["target"]:
                # Показываем диалог выбора целевого виджета
                targets = []
                for w in self.widgets:
                    if str(w.id) != self.current_logic_widget:
                        targets.append(f"{w.widget_type} (ID: {w.id}) - {w.config.get('text', '')[:20]}")

                if targets:
                    from tkinter import simpledialog
                    target_win = tk.Toplevel()
                    target_win.title("Выберите целевой виджет")
                    target_win.geometry("300x200")

                    listbox = tk.Listbox(target_win)
                    listbox.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
                    for t in targets:
                        listbox.insert(tk.END, t)

                    def select():
                        if listbox.curselection():
                            new_rule["target"] = listbox.get(listbox.curselection()[0])
                        target_win.destroy()

                    ttk.Button(target_win, text="Выбрать", command=select).pack(pady=5)
                    target_win.wait_window()

            self.logic_rules[self.current_logic_widget].append(new_rule)

        self.refresh_logic_display()
    def edit_event_code(self, event_name, entry_widget):
        """Редактор кода события"""
        win = tk.Toplevel(self.root)
        win.title(f"Редактор события: {event_name}")
        win.geometry("500x400")

        ttk.Label(win, text=f"Код для события {event_name}", font=("Arial", 10, "bold")).pack(pady=5)
        ttk.Label(win, text="def handler(event):\n    # Ваш код здесь\n    pass",
                  font=("Consolas", 8), foreground="gray").pack(anchor=tk.W, padx=10)

        text = tk.Text(win, font=("Consolas", 10), wrap=tk.WORD, height=15)
        text.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        text.insert("1.0", entry_widget.get())

        def save():
            entry_widget.delete(0, tk.END)
            entry_widget.insert(0, text.get("1.0", "end-1c"))
            win.destroy()
            self.update_property("event")

        ttk.Button(win, text="💾 Сохранить", command=save).pack(pady=5)

    def update_property_panel(self):
        """Обновляет панель свойств в зависимости от выбранного виджета"""
        # Очистить текущие свойства
        for widget in self.prop_inner.winfo_children():
            widget.destroy()
        self.prop_widgets.clear()

        if not self.selected_widgets:
            ttk.Label(self.prop_inner, text="Ничего не выбрано", foreground="gray").pack(pady=20)
            return

        wo = next((w for w in self.widgets if str(w.id) == self.selected_widgets[0]), None)
        if not wo:
            return

        wt = wo.widget_type

        # ========== ИНФОРМАЦИЯ ==========
        info_frame = ttk.LabelFrame(self.prop_inner, text="ℹ️ Информация", padding=5)
        info_frame.pack(fill=tk.X, pady=5, padx=5)
        ttk.Label(info_frame, text=f"Тип: {wt}", font=("Arial", 9, "bold")).pack(anchor=tk.W)
        ttk.Label(info_frame, text=f"ID: {wo.id}").pack(anchor=tk.W)

        # ========== ПОЗИЦИЯ ==========
        pos_frame = ttk.LabelFrame(self.prop_inner, text="📐 Позиция и размер", padding=5)
        pos_frame.pack(fill=tk.X, pady=5, padx=5)
        self._add_prop_row(pos_frame, "x", "X:", wo.x, "int")
        self._add_prop_row(pos_frame, "y", "Y:", wo.y, "int")
        self._add_prop_row(pos_frame, "width", "Ширина:", wo.current_width, "int")
        self._add_prop_row(pos_frame, "height", "Высота:", wo.current_height, "int")

        # ========== ТЕКСТ ==========
        if wt in ["Label", "Button", "Checkbutton", "Radiobutton", "Menubutton", "Entry"]:
            text_frame = ttk.LabelFrame(self.prop_inner, text="📝 Текст", padding=5)
            text_frame.pack(fill=tk.X, pady=5, padx=5)

            current_text = wo.config.get("text", "")
            self._add_prop_row(text_frame, "text", "Текст:", current_text, "str")

        # ========== ЦВЕТА ==========
        color_frame = ttk.LabelFrame(self.prop_inner, text="🎨 Цвета", padding=5)
        color_frame.pack(fill=tk.X, pady=5, padx=5)
        self._add_color_row(color_frame, "bg", "Фон:", wo.config.get("bg", "#f0f0f0"))
        self._add_color_row(color_frame, "fg", "Текст:", wo.config.get("fg", "black"))

        # Обновить позицию скролла
        self.prop_inner.update_idletasks()

    def update_logic_panel(self):
        """Обновляет панель логики для выбранного виджета"""
        if not self.selected_widgets:
            self.logic_widget_var.set("Ничего не выбрано")
            self.current_logic_widget = None
            self.refresh_logic_display()
            return

        wo = next((w for w in self.widgets if str(w.id) == self.selected_widgets[0]), None)
        if wo:
            self.logic_widget_var.set(f"{wo.widget_type} (ID: {wo.id})")
            self.current_logic_widget = str(wo.id)
            self.refresh_logic_display()
        else:
            self.current_logic_widget = None

    def refresh_logic_display(self):
        """Обновляет отображение правил"""
        if not hasattr(self, 'logic_inner'):
            return

        for child in self.logic_inner.winfo_children():
            child.destroy()

        if not self.current_logic_widget or self.current_logic_widget not in self.logic_rules:
            empty_label = ttk.Label(self.logic_inner, text="Нет правил для этого виджета\nНажмите 'Добавить правило'",
                                    justify=tk.CENTER, foreground="gray")
            empty_label.pack(expand=True, fill=tk.BOTH, pady=50)
            return
    def _add_prop_row(self, parent, key, label, value, value_type="str"):
        """Добавляет строку свойства с ПРАВИЛЬНЫМ сохранением"""
        frame = ttk.Frame(parent)
        frame.pack(fill=tk.X, pady=2)
        ttk.Label(frame, text=label, width=15).pack(side=tk.LEFT)

        var = tk.StringVar(value=str(value))
        entry = ttk.Entry(frame, textvariable=var, width=20)
        entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(5, 0))

        # Функция сохранения при потере фокуса
        def save_on_focus(event=None):
            new_value = var.get()
            if value_type == "int":
                try:
                    new_value = int(new_value) if new_value else 0
                except:
                    new_value = 0
            # Прямой вызов обновления
            self._update_widget_property(key, new_value)

        # Сохраняем при потере фокуса и при нажатии Enter
        entry.bind("<FocusOut>", save_on_focus)
        entry.bind("<Return>", save_on_focus)

        self.prop_widgets[key] = (var, value_type, entry)

    def _add_color_row(self, parent, key, label, value):
        """Добавляет строку выбора цвета"""
        frame = ttk.Frame(parent)
        frame.pack(fill=tk.X, pady=2)
        ttk.Label(frame, text=label, width=15).pack(side=tk.LEFT)

        var = tk.StringVar(value=str(value))
        entry = ttk.Entry(frame, textvariable=var, width=17)
        entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(5, 2))

        def pick_color():
            color = colorchooser.askcolor(var.get())[1]
            if color:
                var.set(color)
                self._update_widget_property(key, color)

        ttk.Button(frame, text="🎨", width=3, command=pick_color).pack(side=tk.LEFT)

        def save_on_focus(event=None):
            self._update_widget_property(key, var.get())

        entry.bind("<FocusOut>", save_on_focus)
        entry.bind("<Return>", save_on_focus)

        self.prop_widgets[key] = (var, "color", entry)

    def _add_option_row(self, parent, key, label, value, options):
        """Добавляет строку с выпадающим списком"""
        frame = ttk.Frame(parent)
        frame.pack(fill=tk.X, pady=2)
        ttk.Label(frame, text=label, width=15).pack(side=tk.LEFT)

        var = tk.StringVar(value=str(value))
        combo = ttk.Combobox(frame, textvariable=var, values=options, width=18)
        combo.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(5, 0))

        self.prop_widgets[key] = (var, "option")
        var.trace_add("write", lambda *a, k=key: self._on_prop_change(k, var.get()))

    def _add_checkbox_row(self, parent, key, label, value):
        """Добавляет строку с чекбоксом"""
        var = tk.BooleanVar(value=value)
        cb = ttk.Checkbutton(parent, text=label, variable=var,
                             command=lambda: self._on_prop_change(key, var.get()))
        cb.pack(anchor=tk.W, pady=2)
        self.prop_widgets[key] = (var, "bool")

    def _pick_color(self, key, var):
        """Выбор цвета"""
        color = colorchooser.askcolor(var.get())[1]
        if color:
            var.set(color)

    def _on_prop_change(self, key, value):
        """Обработчик изменения свойства"""
        if not self.selected_widgets:
            return
        wo = next((w for w in self.widgets if str(w.id) == self.selected_widgets[0]), None)
        if not wo:
            return

        # Преобразование типов
        if key in ["x", "y", "width", "height"]:
            try:
                value = int(float(value))
            except:
                value = 0

        if key in ["x", "y"]:
            setattr(wo, key, value)
            if wo.widget_instance:
                self.canvas.coords(wo.widget_instance, wo.x, wo.y)
        elif key in ["width", "height"]:
            setattr(wo, f"current_{key}", value)
            if wo.frame:
                wo.frame.config(**{key: value})
                self.canvas.coords(wo.widget_instance, wo.x, wo.y)
        else:
            wo.config[key] = value

        # ВАЖНО: Перерисовываем виджет для применения изменений
        self.render_widget(wo)  # ← ЭТО КЛЮЧЕВОЙ МОМЕНТ!

        # Обновить выделение
        if wo.selection_rect:
            self._upd_sel_bounds(wo)

        self.undo_manager.save_state(f"Изменено {key}")
    def _quick_spin_setup(self, wo):
        """Быстрая настройка Spinbox"""
        win = tk.Toplevel(self.root)
        win.title("Настройка Spinbox")
        win.geometry("300x250")
        win.transient(self.root)

        ttk.Label(win, text="Минимум:", font=("Arial", 9)).pack(pady=(10, 0))
        from_var = tk.StringVar(value=str(wo.config.get("from_", 0)))
        ttk.Entry(win, textvariable=from_var).pack(pady=5)

        ttk.Label(win, text="Максимум:").pack(pady=(10, 0))
        to_var = tk.StringVar(value=str(wo.config.get("to", 100)))
        ttk.Entry(win, textvariable=to_var).pack(pady=5)

        ttk.Label(win, text="Шаг:").pack(pady=(10, 0))
        step_var = tk.StringVar(value=str(wo.config.get("increment", 1)))
        ttk.Entry(win, textvariable=step_var).pack(pady=5)

        def apply():
            wo.config["from_"] = int(from_var.get())
            wo.config["to"] = int(to_var.get())
            wo.config["increment"] = int(step_var.get())
            self.render_widget(wo)
            win.destroy()
            self.update_property_panel()

        ttk.Button(win, text="Применить", command=apply).pack(pady=15)

    def _edit_list_items(self, wo):
        """Редактор элементов Combobox"""
        win = tk.Toplevel(self.root)
        win.title("Редактор списка")
        win.geometry("400x350")
        win.transient(self.root)

        current = wo.config.get("values", "")
        items = [v.strip() for v in current.split(",") if v.strip()]

        frame = ttk.Frame(win)
        frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        listbox = tk.Listbox(frame)
        listbox.pack(fill=tk.BOTH, expand=True)

        for item in items:
            listbox.insert(tk.END, item)

        entry_frame = ttk.Frame(win)
        entry_frame.pack(fill=tk.X, padx=10, pady=5)

        entry = ttk.Entry(entry_frame)
        entry.pack(side=tk.LEFT, fill=tk.X, expand=True)

        def add():
            if entry.get():
                listbox.insert(tk.END, entry.get())
                entry.delete(0, tk.END)

        def remove():
            if listbox.curselection():
                listbox.delete(listbox.curselection()[0])

        ttk.Button(entry_frame, text="➕", width=3, command=add).pack(side=tk.LEFT, padx=2)
        ttk.Button(entry_frame, text="✖️", width=3, command=remove).pack(side=tk.LEFT, padx=2)

        def save():
            new_items = [listbox.get(i) for i in range(listbox.size())]
            wo.config["values"] = ",".join(new_items)
            self.render_widget(wo)
            win.destroy()
            self.update_property_panel()

        ttk.Button(win, text="💾 Сохранить", command=save).pack(pady=5)

    def _edit_listbox_items(self, wo):
        """Редактор элементов Listbox"""
        self._edit_list_items(wo)  # Используем ту же логику

    def _edit_menu_items(self, wo):
        """Редактор меню для Menubutton"""
        win = tk.Toplevel(self.root)
        win.title("Редактор меню")
        win.geometry("450x400")
        win.transient(self.root)

        ttk.Label(win, text="Пункты меню (по одному на строку):").pack(pady=5)
        text = tk.Text(win, font=("Consolas", 10), height=15)
        text.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)

        current = wo.config.get("menu_items", "Пункт 1\nПункт 2\n---\nВыход")
        text.insert("1.0", current)

        def save():
            items = text.get("1.0", "end-1c").strip()
            wo.config["menu_items"] = items
            self.render_widget(wo)
            win.destroy()
            self.update_property_panel()

        ttk.Button(win, text="💾 Сохранить", command=save).pack(pady=5)

    def _quick_progress_set(self, wo, value):
        """Быстрая настройка Progressbar"""
        wo.config["value"] = value
        self.render_widget(wo)
    def _add_simple_prop(self, parent, key, label, value):
        """Добавляет простое текстовое свойство"""
        frame = ttk.Frame(parent)
        frame.pack(fill=tk.X, pady=2)
        ttk.Label(frame, text=label, width=10).pack(side=tk.LEFT)
        var = tk.StringVar(value=str(value))
        entry = ttk.Entry(frame, textvariable=var, width=15)
        entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(5, 0))
        self.prop_widgets[key] = var
        var.trace_add("write", lambda *a, k=key: self._on_prop_change(k, var.get()))

    def _add_color_prop(self, parent, key, label, value):
        """Добавляет свойство цвета с кнопкой выбора"""
        frame = ttk.Frame(parent)
        frame.pack(fill=tk.X, pady=2)
        ttk.Label(frame, text=label, width=10).pack(side=tk.LEFT)
        var = tk.StringVar(value=str(value))
        entry = ttk.Entry(frame, textvariable=var, width=12)
        entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(5, 2))
        ttk.Button(frame, text="🎨", width=3,
                   command=lambda k=key, v=var: self._pick_color(k, v)).pack(side=tk.LEFT)
        self.prop_widgets[key] = var
        var.trace_add("write", lambda *a, k=key: self._on_prop_change(k, var.get()))

    def _pick_color(self, key, var):
        """Выбор цвета"""
        color = colorchooser.askcolor(var.get())[1]
        if color:
            var.set(color)

    def _on_prop_change(self, key, value):
        """Обработчик изменения свойства"""
        if not self.selected_widgets:
            return
        wo = next((w for w in self.widgets if str(w.id) == self.selected_widgets[0]), None)
        if not wo:
            return

        # Преобразование типов
        if key in ["x", "y", "width", "height"]:
            try:
                value = int(float(value))
            except:
                value = 0

        if key in ["x", "y"]:
            setattr(wo, key, value)
            if wo.widget_instance:
                self.canvas.coords(wo.widget_instance, wo.x, wo.y)
        elif key in ["width", "height"]:
            setattr(wo, f"current_{key}", value)
            if wo.frame:
                wo.frame.config(**{key: value})
                self.canvas.coords(wo.widget_instance, wo.x, wo.y)
        else:
            wo.config[key] = value

        # Обновить выделение и перерисовать
        if wo.selection_rect:
            self._upd_sel_bounds(wo)
        self.undo_manager.save_state(f"Изменено {key}")
    def _rebuild_palette(self):
        for c in self.palette_frame.winfo_children():
            c.destroy()
        self.widget_buttons.clear()
        q = self.search_var.get().lower()
        for wt, wn in WIDGET_TYPES:
            if q and q not in wt.lower() and q not in wn.lower():
                continue
            btn = ttk.Button(self.palette_frame,
                             text=f"{ICONS.get(wt,'')} {wn}",
                             command=lambda t=wt: self.set_add_mode(t))
            btn.pack(fill=tk.X, pady=1, ipady=2)
            self.widget_buttons[wt] = btn
            tip = WIDGET_TOOLTIPS.get(wt,"")
            if tip:
                Tooltip(btn, tip)
        self.toolbar_canvas.update_idletasks()
        bb = self.toolbar_canvas.bbox("all")
        if bb:
            self.toolbar_canvas.configure(scrollregion=bb)

    def _pointer_over_toolbar(self, event):
        """Курсор над левой панелью (включая полосу прокрутки)."""
        tf = getattr(self, "tool_frame", None)
        if not tf:
            return False
        try:
            w = self.root.winfo_containing(event.x_root, event.y_root)
        except Exception:
            return False
        while w:
            if w == tf:
                return True
            if w == self.root:
                return False
            try:
                par = w.winfo_parent()
                if not par:
                    return False
                w = self.root.nametowidget(par)
            except Exception:
                return False

    def bind_keys(self):
        r = self.root
        r.bind("<Control-z>",       lambda e: self.undo_manager.undo())
        r.bind("<Control-y>",       lambda e: self.undo_manager.redo())
        r.bind("<Control-c>",       lambda e: self.copy_selection())
        r.bind("<Control-v>",       lambda e: self.paste_selection())
        r.bind("<Control-x>",       lambda e: self.cut_selection())
        r.bind("<Control-d>",       lambda e: self._duplicate())
        r.bind("<Delete>",          lambda e: self.delete_selected())
        r.bind("<Control-g>",       lambda e: self.group_selected())
        r.bind("<Escape>",          lambda e: self._esc())
        for key, dx, dy in [("<Left>",-1,0),("<Right>",1,0),("<Up>",0,-1),("<Down>",0,1),
                             ("<Shift-Left>",-10,0),("<Shift-Right>",10,0),
                             ("<Shift-Up>",0,-10),("<Shift-Down>",0,10)]:
            r.bind(key, lambda e, x=dx, y=dy: self._nudge(x,y))

    # ── ZOOM / PAN ────────────────────────────────────────────────────────────
    def zoom_in(self):
        if self.zoom_level < 4.0:
            self.zoom_level = min(self.zoom_level*1.2, 4.0)
            self.canvas.scale("all",0,0,1.2,1.2)
            self.update_status(f"Масштаб: {int(self.zoom_level*100)}%")

    def zoom_out(self):
        if self.zoom_level > 0.2:
            self.zoom_level /= 1.2
            self.canvas.scale("all",0,0,1/1.2,1/1.2)
            self.update_status(f"Масштаб: {int(self.zoom_level*100)}%")

    def toggle_pan_mode(self):
        if self.current_mode == "pan":
            self.current_mode = "move"
            self.mode_label.config(text="Режим: Перемещение")
            self.canvas.config(cursor="")
        else:
            self.current_mode = "pan"
            self.mode_label.config(text="Режим: Панорама")
            self.canvas.config(cursor="fleur")

    def on_mouse_wheel(self, event):
        self.zoom_in() if event.delta > 0 else self.zoom_out()

    def on_pan_start(self, event):
        self.pan_start = (event.x, event.y)
        self.canvas.config(cursor="fleur")

    def on_pan_drag(self, event):
        if self.pan_start:
            self.canvas.scan_dragto(event.x, event.y, gain=1)
            self.pan_start = (event.x, event.y)
            self._draw_rulers()

    def on_pan_release(self, event):
        self.pan_start = None
        if self.current_mode != "pan":
            self.canvas.config(cursor="")

    def _esc(self):
        self.current_mode = "move"
        self.mode_label.config(text="Режим: Перемещение")
        self.canvas.config(cursor="")

    # ── GRID & RULERS ─────────────────────────────────────────────────────────
    def toggle_grid(self):
        self.snap_to_grid = self.snap_var.get()
        self.draw_grid()

    def draw_grid(self):
        self.canvas.delete("grid")
        if not self.snap_to_grid:
            return
        for i in range(0, 3000, self.grid_size):
            self.canvas.create_line(i, 0, i, 3000, fill="#eeeeee", tags="grid")
            self.canvas.create_line(0, i, 3000, i,  fill="#eeeeee", tags="grid")
        self.canvas.tag_lower("grid")
        self.update_canvas_scrollregion()

    def update_canvas_scrollregion(self):
        """Размер виртуального холста: прокрутка вниз/вправо к нижним виджетам и к сетке."""
        max_x = 900
        max_y = 700
        for wo in self.widgets:
            if not getattr(wo, "visible", True):
                continue
            max_x = max(max_x, wo.x + wo.current_width + 120)
            max_y = max(max_y, wo.y + wo.current_height + 120)
        if getattr(self, "snap_to_grid", True):
            max_x = max(max_x, 3000)
            max_y = max(max_y, 3000)
        else:
            max_x = max(max_x, 1600)
            max_y = max(max_y, 1200)
        self.canvas.configure(
            scrollregion=(0, 0, min(max_x, 12000), min(max_y, 12000)),
        )

    def _draw_rulers(self):
        try:
            x0 = int(self.canvas.canvasx(0))
            y0 = int(self.canvas.canvasy(0))
        except Exception:
            x0, y0 = 0, 0

        # Horizontal
        rw = max(self.ruler_h.winfo_width(), 1)
        rh = max(self.ruler_h.winfo_height(), 20)
        self.ruler_h.delete("all")
        self.ruler_h.create_rectangle(0,0,rw,rh, fill="#f0f0f0", outline="")
        step = 50
        s = (x0//step)*step
        for px in range(s, x0+rw+step, step):
            x = px-x0
            tk_ = 12 if px%100==0 else 5
            self.ruler_h.create_line(x, rh-tk_, x, rh, fill="#999")
            if px%100==0:
                self.ruler_h.create_text(x+2, 2, text=str(px), anchor="nw",
                                         font=("Arial",7), fill="#555")
        for g in self.guides:
            if g["type"]=="v":
                gx = g["pos"]-x0
                self.ruler_h.create_rectangle(gx-2,0,gx+2,rh, fill="#1a6bff", outline="")

        # Vertical
        vw = max(self.ruler_v.winfo_width(), 20)
        vh = max(self.ruler_v.winfo_height(), 1)
        self.ruler_v.delete("all")
        self.ruler_v.create_rectangle(0,0,vw,vh, fill="#f0f0f0", outline="")
        s = (y0//step)*step
        for py in range(s, y0+vh+step, step):
            y = py-y0
            tk_ = 12 if py%100==0 else 5
            self.ruler_v.create_line(vw-tk_, y, vw, y, fill="#999")
            if py%100==0:
                self.ruler_v.create_text(2, y+2, text=str(py), anchor="nw",
                                         font=("Arial",7), fill="#555")
        for g in self.guides:
            if g["type"]=="h":
                gy = g["pos"]-y0
                self.ruler_v.create_rectangle(0,gy-2,vw,gy+2, fill="#1a6bff", outline="")

    def _canvas_motion(self, event):
        try:
            cx = int(self.canvas.canvasx(event.x))
            cy = int(self.canvas.canvasy(event.y))
            self.update_status(f"x={cx}  y={cy}")
        except Exception:
            pass

    # ── GUIDES ────────────────────────────────────────────────────────────────
    def _rh_press(self, event):   # horizontal ruler → vertical guide
        try:   cx = int(self.canvas.canvasx(event.x))
        except: cx = event.x
        gid = self.canvas.create_line(cx,0,cx,3000, fill="#1a6bff",
                                       dash=(5,3), width=1, tags="guide_line")
        self.temp_guide_id = gid; self.temp_guide_type = "v"; self.temp_guide_pos = cx

    def _rh_drag(self, event):
        if not self.temp_guide_id: return
        try:   cx = int(self.canvas.canvasx(event.x))
        except: cx = event.x
        self.canvas.coords(self.temp_guide_id, cx,0,cx,3000)
        self.temp_guide_pos = cx

    def _rh_release(self, _):
        if self.temp_guide_id:
            self.guides.append({"type":"v","pos":self.temp_guide_pos,"id":self.temp_guide_id})
            self.temp_guide_id = None
            self._draw_rulers()

    def _rv_press(self, event):   # vertical ruler → horizontal guide
        try:   cy = int(self.canvas.canvasy(event.y))
        except: cy = event.y
        gid = self.canvas.create_line(0,cy,3000,cy, fill="#1a6bff",
                                       dash=(5,3), width=1, tags="guide_line")
        self.temp_guide_id = gid; self.temp_guide_type = "h"; self.temp_guide_pos = cy

    def _rv_drag(self, event):
        if not self.temp_guide_id: return
        try:   cy = int(self.canvas.canvasy(event.y))
        except: cy = event.y
        self.canvas.coords(self.temp_guide_id, 0,cy,3000,cy)
        self.temp_guide_pos = cy

    def _rv_release(self, _):
        if self.temp_guide_id:
            self.guides.append({"type":"h","pos":self.temp_guide_pos,"id":self.temp_guide_id})
            self.temp_guide_id = None
            self._draw_rulers()

    def clear_guides(self):
        for g in self.guides:
            self.canvas.delete(g["id"])
        self.guides.clear()
        self._draw_rulers()

    # ── MINIMAP ───────────────────────────────────────────────────────────────
    def _init_minimap(self):
        mm = tk.Frame(self.canvas, bg="#ccc", bd=1, relief=tk.SOLID)
        mm.place(relx=1.0, rely=1.0, anchor="se", x=-4, y=-4)

        hdr = tk.Frame(mm, bg="#444")
        hdr.pack(fill=tk.X)
        tk.Label(hdr, text=" Миникарта", bg="#444", fg="white",
                 font=("Arial",7,"bold")).pack(side=tk.LEFT)
        tk.Button(hdr, text="×", bg="#444", fg="white", relief=tk.FLAT, bd=0,
                  font=("Arial",7), command=mm.place_forget).pack(side=tk.RIGHT)

        self.minimap_canvas = tk.Canvas(mm, width=190, height=120,
                                        bg="#fafafa", highlightthickness=0)
        self.minimap_canvas.pack()
        self._update_minimap()

    def _update_minimap(self):
        mc = self.minimap_canvas
        if mc is None:
            return
        mc.delete("all")
        if not self.widgets:
            mc.create_text(95,60, text="(пусто)", fill="#bbb", font=("Arial",9))
            return
        xs = [w.x for w in self.widgets]+[w.x+w.current_width  for w in self.widgets]
        ys = [w.y for w in self.widgets]+[w.y+w.current_height for w in self.widgets]
        mnx,mxx = min(xs,default=0), max(xs,default=400)
        mny,mxy = min(ys,default=0), max(ys,default=300)
        sx = 180/max(mxx-mnx,200)
        sy = 110/max(mxy-mny,150)
        sc = min(sx,sy)
        FILLS = {"Label":"#a8d8ea","Button":"#ffcf77","Entry":"#fff8e1",
                 "Frame":"#ddd","Canvas":"#c8f7c5","Text":"#f9e4b7",
                 "Progressbar":"#b5ead7","Combobox":"#ffd6e0"}
        for w in self.widgets:
            x1 = 5+(w.x-mnx)*sc; y1 = 5+(w.y-mny)*sc
            x2 = x1+max(w.current_width*sc,3); y2 = y1+max(w.current_height*sc,2)
            fill = FILLS.get(w.widget_type,"#e0e0ff")
            out  = "#1a6bff" if str(w.id) in self.selected_widgets else "#aaa"
            mc.create_rectangle(x1,y1,x2,y2, fill=fill, outline=out, width=1)

    # ── MODE ──────────────────────────────────────────────────────────────────
    def set_add_mode(self, wt):
        self.current_mode = "add"
        self.current_widget_type = wt
        self.mode_label.config(text=f"Режим: Добавление {ICONS.get(wt,'')} {wt}")
        self.deselect_all()

    # ── CANVAS EVENTS ─────────────────────────────────────────────────────────
    def on_canvas_press(self, event):
        if self.current_mode == "add":
            self.place_widget(event.x, event.y); return
        if self.current_mode == "pan":
            self.on_pan_start(event); return

        # Guide drag?
        for g in self.guides:
            if g["type"]=="v" and abs(event.x-g["pos"])<=5:
                self.dragging_guide = g; return
            if g["type"]=="h" and abs(event.y-g["pos"])<=5:
                self.dragging_guide = g; return

        # Resize handle?
        for wo in self.widgets:
            for i,hid in enumerate(wo.resize_handles):
                cc = self.canvas.coords(hid)
                if len(cc)==4:
                    x1,y1,x2,y2 = cc
                    if x1<=event.x<=x2 and y1<=event.y<=y2:
                        self.drag_data.update({
                            "resizing":True,"resize_widget":wo,"resize_handle_idx":i,
                            "start_x":event.x,"start_y":event.y,
                            "orig_x":wo.x,"orig_y":wo.y,
                            "orig_w":wo.current_width,"orig_h":wo.current_height})
                        return

        # Widget click?
        clicked = None
        for wo in reversed(self.widgets):
            if not wo.visible: continue
            if (wo.x<=event.x<=wo.x+wo.current_width and
                    wo.y<=event.y<=wo.y+wo.current_height):
                clicked = wo; break

        if clicked:
            if clicked.locked: return
            if event.state & 0x1:   # Shift
                wid = str(clicked.id)
                if wid in self.selected_widgets: self.selected_widgets.remove(wid)
                else:                            self.selected_widgets.append(wid)
                self.select_widgets(self.selected_widgets); return
            if clicked.group_id:
                grp = [str(w.id) for w in self.widgets if w.group_id==clicked.group_id]
                self.deselect_all(); self.selected_widgets = grp
            elif str(clicked.id) not in self.selected_widgets:
                self.deselect_all(); self.selected_widgets = [str(clicked.id)]
            self.select_widgets(self.selected_widgets)
            self.drag_data["start_x"]=event.x; self.drag_data["start_y"]=event.y
            self.drag_data["resizing"]=False
        else:
            self.deselect_all(); self.drag_data["resizing"]=False

    def on_canvas_drag(self, event):
        # Guide move
        if self.dragging_guide:
            g = self.dragging_guide
            if g["type"]=="v":
                self.canvas.coords(g["id"],event.x,0,event.x,3000); g["pos"]=event.x
            else:
                self.canvas.coords(g["id"],0,event.y,3000,event.y); g["pos"]=event.y
            self._draw_rulers(); return

        # Resize
        if self.drag_data.get("resizing") and self.drag_data.get("resize_widget"):
            wo  = self.drag_data["resize_widget"]
            idx = self.drag_data["resize_handle_idx"]
            dx  = event.x - self.drag_data["start_x"]
            dy  = event.y - self.drag_data["start_y"]
            ox,oy = self.drag_data["orig_x"], self.drag_data["orig_y"]
            ow,oh = self.drag_data["orig_w"], self.drag_data["orig_h"]
            nx,ny,nw,nh = ox,oy,ow,oh
            mw,mh = 30,20
            if idx==0: nx,ny,nw,nh = ox+dx,oy+dy,ow-dx,oh-dy
            elif idx==1: ny,nh = oy+dy,oh-dy
            elif idx==2: ny,nw,nh = oy+dy,ow+dx,oh-dy
            elif idx==3: nw = ow+dx
            elif idx==4: nw,nh = ow+dx,oh+dy
            elif idx==5: nh = oh+dy
            elif idx==6: nx,nw,nh = ox+dx,ow-dx,oh+dy
            elif idx==7: nx,nw = ox+dx,ow-dx
            if nw<mw:
                if idx in [0,6,7]: nx = ox+ow-mw
                nw=mw
            if nh<mh:
                if idx in [0,1,2]: ny = oy+oh-mh
                nh=mh
            if self.snap_to_grid:
                nx=round(nx/self.grid_size)*self.grid_size
                ny=round(ny/self.grid_size)*self.grid_size
                nw=max(mw,round(nw/self.grid_size)*self.grid_size)
                nh=max(mh,round(nh/self.grid_size)*self.grid_size)
            wo.x,wo.y = nx,ny
            wo.current_width,wo.current_height = nw,nh
            wo.config["width"]  = max(1,int(nw/8))
            wo.config["height"] = max(1,int(nh/20))
            if wo.frame:
                wo.frame.config(width=nw, height=nh)
                self.canvas.coords(wo.widget_instance, nx, ny)
            self._upd_sel_bounds(wo); return

        if self.current_mode == "pan":
            self.on_pan_drag(event); return

        # Move
        if self.selected_widgets and not self.drag_data.get("resizing"):
            dx = event.x - self.drag_data["start_x"]
            dy = event.y - self.drag_data["start_y"]
            moved = []
            for wid in self.selected_widgets:
                wo = next((w for w in self.widgets if str(w.id)==wid), None)
                if wo and wo not in moved:
                    moved.append(wo)
                    if wo.group_id:
                        for w in self.widgets:
                            if w.group_id==wo.group_id and w not in moved:
                                moved.append(w)
            for wo in moved:
                if wo.locked: continue
                nx=wo.x+dx; ny=wo.y+dy
                if self.snap_to_grid:
                    nx=round(nx/self.grid_size)*self.grid_size
                    ny=round(ny/self.grid_size)*self.grid_size
                adx,ady = nx-wo.x, ny-wo.y
                if wo.widget_instance:
                    c = self.canvas.coords(wo.widget_instance)
                    self.canvas.coords(wo.widget_instance, c[0]+adx, c[1]+ady)
                if wo.selection_rect:
                    self.canvas.move(wo.selection_rect, adx, ady)
                for h in wo.resize_handles:
                    self.canvas.move(h, adx, ady)
                wo.x,wo.y = nx,ny
            self.drag_data["start_x"]=event.x; self.drag_data["start_y"]=event.y

    def on_canvas_release(self, event):
        if self.dragging_guide:
            self.dragging_guide = None; return
        if self.drag_data.get("resizing") or self.selected_widgets:
            lbl = "Изменение размера" if self.drag_data.get("resizing") else "Перемещение"
            self.undo_manager.save_state(lbl)
        self.drag_data["resizing"]=False
        self.drag_data["resize_widget"]=None
        self.drag_data["resize_handle_idx"]=None
        self.drag_data["items"]=[]
        if self.current_mode=="add":
            self.current_mode="move"
            self.mode_label.config(text="Режим: Перемещение")
        self._update_minimap()
        self.update_canvas_scrollregion()

    def on_canvas_double_click(self, event):
        if self.current_widget_type:
            self.place_widget(event.x, event.y)

    # ── PLACE / RENDER ────────────────────────────────────────────────────────
    def place_widget(self, x, y):
        """Создает новый виджет с правильными начальными свойствами"""
        if self.snap_to_grid:
            x = round(x / self.grid_size) * self.grid_size
            y = round(y / self.grid_size) * self.grid_size

        DEFAULTS = {
            "Label": {"text": "Label", "bg": "#f0f0f0", "fg": "black", "width": 8, "height": 1},
            "Button": {"text": "Button", "bg": "#e0e0e0", "fg": "black", "width": 8, "height": 1},
            "Entry": {"text": "", "bg": "white", "fg": "black", "width": 12},
            "Checkbutton": {"text": "Check", "bg": "#f0f0f0", "fg": "black", "width": 8, "height": 1},
            "Radiobutton": {"text": "Radio", "bg": "#f0f0f0", "fg": "black", "width": 8, "height": 1},
            "Listbox": {"bg": "white", "fg": "black", "width": 12, "height": 4},
            "Text": {"bg": "white", "fg": "black", "width": 20, "height": 3},
            "Spinbox": {"from_": 0, "to": 100, "width": 8},
            "Combobox": {"values": "Вариант 1,Вариант 2", "width": 12},
            "Progressbar": {"value": 50, "length": 120, "mode": "determinate"},
            "Menubutton": {"text": "Меню ▾", "bg": "#e0e0e0", "fg": "black", "width": 8,
                           "menu_items": "Пункт 1\nПункт 2\n---\nВыход"},
        }

        cfg = DEFAULTS.get(self.current_widget_type, {"text": self.current_widget_type}).copy()

        nw = WidgetItem(self.current_widget_type, x, y, cfg)
        nw.current_width = 80
        nw.current_height = 28

        self.widgets.append(nw)
        self.render_widget(nw)
        self.update_layer_panel()
        self.deselect_all()
        self.selected_widgets = [str(nw.id)]
        self.select_widgets(self.selected_widgets)
        self.undo_manager.save_state(f"Добавлен {self.current_widget_type}")
        self.current_mode = "move"
        self.mode_label.config(text="Режим: Перемещение")
        self._update_minimap()

    def _update_widget_property(self, key, value):
        """Обновляет свойство виджета и сразу меняет на холсте"""
        if not self.selected_widgets:
            return

        wo = next((w for w in self.widgets if str(w.id) == self.selected_widgets[0]), None)
        if not wo:
            return

        print(f"🔄 Обновляем {key} = {value} для {wo.widget_type}")  # Отладка

        # Сохраняем в конфиг
        wo.config[key] = value

        # Для текста - особый случай
        if key == "text":
            # Обновляем текст прямо в существующем виджете
            if wo.frame:
                for child in wo.frame.winfo_children():
                    # Для Label, Button, Checkbutton, Radiobutton
                    if hasattr(child, 'config'):
                        try:
                            child.config(text=value)
                            print(f"✅ Текст обновлен на: {value}")
                        except:
                            pass
                    # Для Entry
                    if hasattr(child, 'delete') and hasattr(child, 'insert'):
                        try:
                            child.delete(0, tk.END)
                            child.insert(0, value)
                            print(f"✅ Entry обновлен: {value}")
                        except:
                            pass
                    break

        # Для позиции
        elif key == "x":
            wo.x = value
            if wo.widget_instance:
                self.canvas.coords(wo.widget_instance, wo.x, wo.y)
        elif key == "y":
            wo.y = value
            if wo.widget_instance:
                self.canvas.coords(wo.widget_instance, wo.x, wo.y)

        # Для размера
        elif key == "width":
            wo.current_width = max(20, value)
            if wo.frame:
                wo.frame.config(width=wo.current_width)
                self.canvas.coords(wo.widget_instance, wo.x, wo.y)
        elif key == "height":
            wo.current_height = max(20, value)
            if wo.frame:
                wo.frame.config(height=wo.current_height)
                self.canvas.coords(wo.widget_instance, wo.x, wo.y)

        # Для цвета
        elif key == "bg":
            if wo.frame:
                wo.frame.config(bg=value)
                for child in wo.frame.winfo_children():
                    if hasattr(child, 'config'):
                        try:
                            child.config(bg=value)
                        except:
                            pass
        elif key == "fg":
            if wo.frame:
                for child in wo.frame.winfo_children():
                    if hasattr(child, 'config'):
                        try:
                            child.config(fg=value)
                        except:
                            pass

        # Обновить выделение
        if wo.selection_rect:
            self._upd_sel_bounds(wo)

        # Сохраняем состояние для undo
        self.undo_manager.save_state(f"Изменено {key}")

        # Обновляем панель свойств чтобы показать актуальные значения
        self.update_property_panel()
    def render_widget(self, wo):
        """Перерисовывает виджет с сохранением логики"""

        # Если виджет уже существует - обновляем его свойства
        if wo.widget_instance and wo.frame:
            # Обновляем существующий виджет
            try:
                # Находим внутренний виджет (первый дочерний элемент frame)
                for child in wo.frame.winfo_children():
                    if hasattr(child, 'config'):
                        # Обновляем текст
                        if "text" in wo.config and hasattr(child, 'config'):
                            try:
                                child.config(text=wo.config.get("text", ""))
                            except:
                                pass

                        # Обновляем фон
                        if "bg" in wo.config and hasattr(child, 'config'):
                            try:
                                child.config(bg=wo.config.get("bg", "#f0f0f0"))
                                wo.frame.config(bg=wo.config.get("bg", "#f0f0f0"))
                            except:
                                pass

                        # Обновляем цвет текста
                        if "fg" in wo.config and hasattr(child, 'config'):
                            try:
                                child.config(fg=wo.config.get("fg", "black"))
                            except:
                                pass

                        # Обновляем шрифт
                        if "font" in wo.config and hasattr(child, 'config'):
                            try:
                                child.config(font=wo.config.get("font"))
                            except:
                                pass

                        # Обновляем значение для Entry
                        if wo.widget_type == "Entry" and "text" in wo.config:
                            try:
                                child.delete(0, tk.END)
                                child.insert(0, wo.config.get("text", ""))
                            except:
                                pass

                        # Обновляем значение для Spinbox
                        if wo.widget_type == "Spinbox":
                            try:
                                if "from_" in wo.config:
                                    child.config(from_=wo.config["from_"])
                                if "to" in wo.config:
                                    child.config(to=wo.config["to"])
                            except:
                                pass

                        # Обновляем значения для Combobox
                        if wo.widget_type == "Combobox" and "values" in wo.config:
                            try:
                                vals = [v.strip() for v in str(wo.config["values"]).split(",") if v.strip()]
                                child.config(values=vals)
                                if vals and child.get() not in vals:
                                    child.set(vals[0])
                            except:
                                pass

                        # Обновляем значение для Scale
                        if wo.widget_type == "Scale":
                            try:
                                if "from_" in wo.config:
                                    child.config(from_=wo.config["from_"])
                                if "to" in wo.config:
                                    child.config(to=wo.config["to"])
                            except:
                                pass

                        # Обновляем значение для Progressbar
                        if wo.widget_type == "Progressbar" and "value" in wo.config:
                            try:
                                child.config(value=wo.config["value"])
                            except:
                                pass

                        break

                # Обновляем размеры
                wo.frame.config(width=wo.current_width, height=wo.current_height)
                self.canvas.coords(wo.widget_instance, wo.x, wo.y)

                # Обновляем выделение если нужно
                if wo.selection_rect:
                    self._upd_sel_bounds(wo)

                self.update_canvas_scrollregion()
                return
            except Exception as e:
                print(f"Ошибка обновления виджета: {e}")

        # Если виджета нет - создаем заново
        if wo.widget_instance:
            self.canvas.delete(wo.widget_instance)
            wo.widget_instance = None
            wo.frame = None

        if not wo.visible:
            self.update_canvas_scrollregion()
            return

        wt = wo.widget_type
        cfg = wo.config

        try:
            bg = cfg.get("bg", "#f0f0f0") or "#f0f0f0"

            frame = tk.Frame(self.canvas, width=wo.current_width, height=wo.current_height,
                             bg=bg, relief=tk.FLAT, bd=0, cursor="fleur")
            frame.propagate(False)
            wo.frame = frame

            def fnt():
                f = cfg.get("font")
                return f if f and str(f).strip() else None

            w = None

            # Создаем виджет в зависимости от типа
            if wt == "Label":
                w = tk.Label(frame, text=cfg.get("text", ""), bg=cfg.get("bg", "#f0f0f0"),
                             fg=cfg.get("fg", "black"), font=fnt())

            elif wt == "Button":
                w = tk.Button(frame, text=cfg.get("text", ""), bg=cfg.get("bg", "#e0e0e0"),
                              fg=cfg.get("fg", "black"), font=fnt())

            elif wt == "Entry":
                w = tk.Entry(frame, width=cfg.get("width", 12), bg=cfg.get("bg", "white"),
                             fg=cfg.get("fg", "black"), font=fnt())
                if cfg.get("text"):
                    w.insert(0, cfg["text"])
                if cfg.get("state") == "readonly":
                    w.config(state="readonly")

            elif wt == "Checkbutton":
                w = tk.Checkbutton(frame, text=cfg.get("text", ""), bg=bg, activebackground=bg,
                                   fg=cfg.get("fg", "black"), font=fnt())

            elif wt == "Radiobutton":
                w = tk.Radiobutton(frame, text=cfg.get("text", ""), bg=bg, activebackground=bg,
                                   fg=cfg.get("fg", "black"), font=fnt())

            elif wt == "Listbox":
                w = tk.Listbox(frame, width=cfg.get("width", 12), height=cfg.get("height", 4),
                               bg=cfg.get("bg", "white"), fg=cfg.get("fg", "black"), font=fnt())

            elif wt == "Text":
                w = tk.Text(frame, width=cfg.get("width", 20), height=cfg.get("height", 3),
                            bg=cfg.get("bg", "white"), fg=cfg.get("fg", "black"), font=fnt(),
                            wrap=cfg.get("wrap", "word"))

            elif wt == "Scale":
                ori = tk.HORIZONTAL if cfg.get("orient", "horizontal") == "horizontal" else tk.VERTICAL
                w = tk.Scale(frame, orient=ori, from_=cfg.get("from_", 0), to=cfg.get("to", 100),
                             length=cfg.get("length", 150))

            elif wt == "Canvas":
                w = tk.Canvas(frame, bg=cfg.get("bg", "white"))

            elif wt == "Frame":
                w = tk.Frame(frame, bg=cfg.get("bg", "#e8e8e8"))
                w.propagate(False)

            elif wt == "Notebook":
                w = ttk.Notebook(frame)
                t1 = ttk.Frame(w)
                ttk.Label(t1, text="Вкладка 1").pack(pady=8)
                w.add(t1, text="Tab 1")

            elif wt == "PanedWindow":
                w = ttk.PanedWindow(frame, orient=tk.HORIZONTAL)
                w.add(ttk.Label(w, text="Панель 1"), weight=1)
                w.add(ttk.Label(w, text="Панель 2"), weight=1)

            elif wt == "Spinbox":
                w = ttk.Spinbox(frame, from_=cfg.get("from_", 0), to=cfg.get("to", 100),
                                increment=cfg.get("increment", 1), width=cfg.get("width", 8))

            elif wt == "Combobox":
                vals = [v.strip() for v in str(cfg.get("values", "")).split(",") if v.strip()]
                w = ttk.Combobox(frame, values=vals, width=cfg.get("width", 12))
                if vals:
                    w.set(vals[0])

            elif wt == "Progressbar":
                w = ttk.Progressbar(frame, mode=cfg.get("mode", "determinate"),
                                    value=cfg.get("value", 50), length=cfg.get("length", 120))

            elif wt == "Scrollbar":
                ori = tk.VERTICAL if cfg.get("orient", "vertical") == "vertical" else tk.HORIZONTAL
                w = tk.Scrollbar(frame, orient=ori)

            elif wt == "Separator":
                ori = tk.HORIZONTAL if cfg.get("orient", "horizontal") == "horizontal" else tk.VERTICAL
                w = ttk.Separator(frame, orient=ori)

            elif wt == "Menubutton":
                w = tk.Menubutton(frame, text=cfg.get("text", "Меню ▾"), bg=cfg.get("bg", "#e0e0e0"),
                                  fg=cfg.get("fg", "black"), relief=tk.RAISED)
                m = tk.Menu(w, tearoff=0)

                # Загружаем пункты меню
                menu_items = cfg.get("menu_items", "Пункт 1\nПункт 2\n---\nВыход")
                for item in menu_items.split("\n"):
                    if item.strip() == "---":
                        m.add_separator()
                    elif item.strip():
                        m.add_command(label=item.strip())
                w["menu"] = m

            else:
                w = tk.Label(frame, text=f"? {wt}", bg="lightyellow")

            if w:
                w.pack(fill=tk.BOTH, expand=True)

            # Привязываем обработчики для перемещения
            def make_handler(obj):
                def on_press(e):
                    if self.current_mode == "add" or obj.locked:
                        return
                    if str(obj.id) not in self.selected_widgets:
                        self.deselect_all()
                        self.selected_widgets = [str(obj.id)]
                        self.select_widgets(self.selected_widgets)
                    obj._drag_start = (e.x_root, e.y_root, obj.x, obj.y)

                def on_drag(e):
                    if not hasattr(obj, "_drag_start"):
                        return
                    sx, sy, ox, oy = obj._drag_start
                    nx = ox + e.x_root - sx
                    ny = oy + e.y_root - sy
                    if self.snap_to_grid:
                        nx = round(nx / self.grid_size) * self.grid_size
                        ny = round(ny / self.grid_size) * self.grid_size
                    obj.x, obj.y = nx, ny
                    self.canvas.coords(obj.widget_instance, nx, ny)
                    if obj.selection_rect:
                        self._upd_sel_bounds(obj)

                def on_release(e):
                    if hasattr(obj, "_drag_start"):
                        del obj._drag_start
                        self.undo_manager.save_state("Перемещение")
                        self._update_minimap()
                        self.update_canvas_scrollregion()

                return on_press, on_drag, on_release

            press, drag, release = make_handler(wo)

            for ww in ([frame, w] if w else [frame]):
                if ww:
                    ww.bind("<Button-1>", press, "+")
                    ww.bind("<B1-Motion>", drag, "+")
                    ww.bind("<ButtonRelease-1>", release, "+")

            wid = self.canvas.create_window(wo.x, wo.y, window=frame, anchor="nw", tags=f"widget_{wo.id}")
            wo.widget_instance = wid

            self.root.update_idletasks()
            rw = frame.winfo_width()
            rh = frame.winfo_height()
            if rw > 1 and rh > 1:
                wo.current_width = rw
                wo.current_height = rh

            if str(wo.id) in self.selected_widgets:
                self.select_widgets(self.selected_widgets)

            self.update_canvas_scrollregion()

        except Exception as e:
            import traceback
            traceback.print_exc()
            ef = tk.Frame(self.canvas, bg="#ffcccc", bd=1, relief=tk.SOLID)
            tk.Label(ef, text=f"⚠ {wt}", bg="#ffcccc").pack(padx=4, pady=2)
            wo.frame = ef
            wo.widget_instance = self.canvas.create_window(wo.x, wo.y, window=ef, anchor="nw")
            self.update_canvas_scrollregion()
    # ── SELECTION ─────────────────────────────────────────────────────────────
    def select_widgets(self, ids):
        self.deselect_all()
        self.selected_widgets = list(ids)
        for wid in ids:
            wo = next((w for w in self.widgets if str(w.id) == wid), None)
            if not wo: continue
            x, y, w, h = wo.x, wo.y, wo.current_width, wo.current_height
            rect = self.canvas.create_rectangle(x - 2, y - 2, x + w + 2, y + h + 2,
                                                outline="#1a6bff", width=2, tags=("selection", f"sel_{wid}"))
            self.canvas.tag_lower(rect)
            wo.selection_rect = rect
            if len(ids) == 1:
                self.draw_resize_handles(wo)
        if ids:
            wo = next((w for w in self.widgets if str(w.id) == ids[0]), None)
            if wo:
                self.update_property_panel()
                self.update_logic_panel()  # ← Обновляем панель логики
        self.update_layer_panel()
        self._update_minimap()

    def update_logic_panel(self):
        """Обновляет панель логики для выбранного виджета"""
        if not self.selected_widgets:
            self.logic_widget_var.set("Ничего не выбрано")
            self.current_logic_widget = None
            self.refresh_logic_display()
            return

        wo = next((w for w in self.widgets if str(w.id) == self.selected_widgets[0]), None)
        if wo:
            self.logic_widget_var.set(f"{wo.widget_type} (ID: {wo.id})")
            self.current_logic_widget = str(wo.id)
            self.refresh_logic_display()
        else:
            self.current_logic_widget = None

    def refresh_logic_display(self):
        """Обновляет отображение правил"""
        for child in self.logic_inner.winfo_children():
            child.destroy()

        if not self.current_logic_widget or self.current_logic_widget not in self.logic_rules:
            empty_label = ttk.Label(self.logic_inner, text="Нет правил для этого виджета\nНажмите 'Добавить правило'",
                                    justify=tk.CENTER, foreground="gray")
            empty_label.pack(expand=True, fill=tk.BOTH, pady=50)
            return

        rules = self.logic_rules[self.current_logic_widget]

        for i, rule in enumerate(rules):
            self.create_rule_widget(i, rule)

    def create_rule_widget(self, index, rule):
        """Создает визуальный блок правила"""
        frame = tk.Frame(self.logic_inner, bg="white", relief=tk.RAISED, bd=1)
        frame.pack(fill=tk.X, padx=10, pady=5)

        # Заголовок
        header = tk.Frame(frame, bg="#4a90d9")
        header.pack(fill=tk.X)
        tk.Label(header, text=f"Правило #{index + 1}", bg="#4a90d9", fg="white",
                 font=("Arial", 9, "bold")).pack(side=tk.LEFT, padx=10, pady=5)
        tk.Button(header, text="✖", bg="#4a90d9", fg="white", bd=0,
                  command=lambda: self.delete_rule(index)).pack(side=tk.RIGHT, padx=10)

        # Тело правила
        body = tk.Frame(frame, bg="white", padx=10, pady=10)
        body.pack(fill=tk.X)

        # КОГДА (Событие)
        tk.Label(body, text="КОГДА:", bg="white", font=("Arial", 9, "bold")).grid(row=0, column=0, sticky=tk.W, pady=5)
        event_var = tk.StringVar(value=rule.get("event", "click"))
        event_combo = ttk.Combobox(body, textvariable=event_var,
                                   values=["click", "double_click", "enter", "leave", "focus", "blur", "key_press"],
                                   width=15, state="readonly")
        event_combo.grid(row=0, column=1, sticky=tk.W, padx=10, pady=5)

        # Описание события
        event_desc = {
            "click": "Нажатие на виджет",
            "double_click": "Двойное нажатие",
            "enter": "Наведение мыши",
            "leave": "Уход мыши",
            "focus": "Фокус",
            "blur": "Потеря фокуса",
            "key_press": "Нажатие клавиши"
        }
        tk.Label(body, text=event_desc.get(rule.get("event", "click"), ""),
                 bg="white", foreground="gray", font=("Arial", 8)).grid(row=0, column=2, sticky=tk.W, pady=5)

        # ТО (Действие)
        tk.Label(body, text="ТО:", bg="white", font=("Arial", 9, "bold")).grid(row=1, column=0, sticky=tk.W, pady=5)
        action_var = tk.StringVar(value=rule.get("action", "set_text"))
        action_combo = ttk.Combobox(body, textvariable=action_var,
                                    values=["set_text", "set_bg", "show_hide", "enable_disable", "set_value",
                                            "call_function"],
                                    width=15, state="readonly")
        action_combo.grid(row=1, column=1, sticky=tk.W, padx=10, pady=5)

        # Целевой виджет
        tk.Label(body, text="ЦЕЛЬ:", bg="white", font=("Arial", 9, "bold")).grid(row=2, column=0, sticky=tk.W, pady=5)

        target_frame = tk.Frame(body, bg="white")
        target_frame.grid(row=2, column=1, sticky=tk.W, padx=10, pady=5)

        target_var = tk.StringVar(value=rule.get("target", ""))
        target_combo = ttk.Combobox(target_frame, textvariable=target_var, width=20)
        target_combo.pack(side=tk.LEFT)

        # Обновить список целевых виджетов
        self.update_target_list(target_combo)

        # Значение
        tk.Label(body, text="ЗНАЧЕНИЕ:", bg="white", font=("Arial", 9, "bold")).grid(row=3, column=0, sticky=tk.W,
                                                                                     pady=5)
        value_var = tk.StringVar(value=rule.get("value", ""))
        value_entry = ttk.Entry(body, textvariable=value_var, width=30)
        value_entry.grid(row=3, column=1, sticky=tk.W, padx=10, pady=5)

        # Условие (если / иначе по смыслу: действие только при выполнении)
        tk.Label(body, text="УСЛОВИЕ:", bg="white", font=("Arial", 9, "bold")).grid(row=4, column=0, sticky=tk.NW,
                                                                                    pady=5)
        cond_frame = tk.Frame(body, bg="white")
        cond_frame.grid(row=4, column=1, sticky=tk.W, padx=10, pady=5)
        condition_var = tk.StringVar(value=rule.get("condition", "always") or "always")
        cond_combo = ttk.Combobox(cond_frame, textvariable=condition_var,
                                  values=["always", "if_equal", "if_not_equal"],
                                  width=18, state="readonly")
        cond_combo.pack(side=tk.LEFT)
        tk.Label(cond_frame, text="(поле A и B — только для сравнения)", bg="white", fg="gray",
                 font=("Arial", 8)).pack(side=tk.LEFT, padx=(8, 0))

        tk.Label(body, text="ПОЛЕ A:", bg="white", font=("Arial", 9, "bold")).grid(row=5, column=0, sticky=tk.W, pady=5)
        compare_a_var = tk.StringVar(value=rule.get("compare_a", "") or "")
        compare_a_combo = ttk.Combobox(body, textvariable=compare_a_var, width=40)
        compare_a_combo.grid(row=5, column=1, sticky=tk.W, padx=10, pady=5)
        self.update_target_list(compare_a_combo)

        tk.Label(body, text="ПОЛЕ B:", bg="white", font=("Arial", 9, "bold")).grid(row=6, column=0, sticky=tk.W, pady=5)
        compare_b_var = tk.StringVar(value=rule.get("compare_b", "") or "")
        compare_b_combo = ttk.Combobox(body, textvariable=compare_b_var, width=40)
        compare_b_combo.grid(row=6, column=1, sticky=tk.W, padx=10, pady=5)
        self.update_target_list(compare_b_combo)

        cond_hint = tk.Label(body, text=self.get_condition_hint(condition_var.get()),
                               bg="white", foreground="gray", font=("Arial", 8))
        cond_hint.grid(row=4, column=2, sticky=tk.W, pady=5)

        # Подсказка по действию
        action_hint = tk.Label(body, text=self.get_action_hint(rule.get("action", "set_text")),
                               bg="white", foreground="gray", font=("Arial", 8))
        action_hint.grid(row=1, column=2, sticky=tk.W, pady=5)

        # Сохранение правила
        def save_rule():
            rule["event"] = event_var.get()
            rule["action"] = action_var.get()
            rule["target"] = target_var.get()
            rule["value"] = value_var.get()
            rule["condition"] = condition_var.get()
            rule["compare_a"] = compare_a_var.get()
            rule["compare_b"] = compare_b_var.get()
            self.logic_status.config(text="Правило сохранено ✓", foreground="green")
            self.root.after(2000, lambda: self.logic_status.config(text=""))

        ttk.Button(body, text="💾 Сохранить", command=save_rule).grid(row=7, column=1, pady=10, sticky=tk.W)

        # Привязка изменения подсказки
        def on_action_change(*args):
            action_hint.config(text=self.get_action_hint(action_var.get()))

        action_var.trace_add("write", on_action_change)

        def on_condition_change(*args):
            cond_hint.config(text=self.get_condition_hint(condition_var.get()))

        condition_var.trace_add("write", on_condition_change)

    def get_condition_hint(self, condition):
        """Подсказка для режима условия"""
        hints = {
            "always": "Действие выполняется всегда (без проверки полей A и B)",
            "if_equal": "Действие только если текст/значение поля A совпадает с полем B (пароль = подтверждение)",
            "if_not_equal": "Действие только если поле A и поле B различаются"
        }
        return hints.get(condition, hints["always"])

    def update_target_list(self, combobox):
        """Обновляет список целевых виджетов"""
        targets = []
        for w in self.widgets:
            target_name = f"{w.widget_type} (ID: {w.id})"
            if w.config.get("text"):
                target_name += f" - {w.config['text'][:20]}"
            targets.append(target_name)
        combobox['values'] = targets

    def get_action_hint(self, action):
        """Возвращает подсказку для действия"""
        hints = {
            "set_text": "Пример: 'Новый текст'",
            "set_bg": "Пример: '#ff0000' или 'red'",
            "show_hide": "Пример: 'show' или 'hide'",
            "enable_disable": "Пример: 'enable' или 'disable'",
            "set_value": "Пример: '50' (для Scale/Progressbar)",
            "call_function": "Пример: 'print(\"Hello\")'"
        }
        return hints.get(action, "Введите значение")

    def add_logic_rule(self):
        """Добавляет новое правило для текущего виджета"""
        if not self.current_logic_widget:
            messagebox.showwarning("Внимание", "Сначала выберите виджет на холсте!")
            return

        if self.current_logic_widget not in self.logic_rules:
            self.logic_rules[self.current_logic_widget] = []

        new_rule = {
            "event": "click",
            "action": "set_text",
            "target": "",
            "value": "",
            "condition": "always",
            "compare_a": "",
            "compare_b": ""
        }
        self.logic_rules[self.current_logic_widget].append(new_rule)
        self.refresh_logic_display()
        self.logic_status.config(text="Правило добавлено ✓", foreground="green")
        self.root.after(2000, lambda: self.logic_status.config(text=""))

    def delete_rule(self, index):
        """Удаляет правило"""
        if self.current_logic_widget and self.current_logic_widget in self.logic_rules:
            del self.logic_rules[self.current_logic_widget][index]
            if not self.logic_rules[self.current_logic_widget]:
                del self.logic_rules[self.current_logic_widget]
            self.refresh_logic_display()
            self.logic_status.config(text="Правило удалено", foreground="orange")

    def clear_all_rules(self):
        """Очищает все правила для текущего виджета"""
        if self.current_logic_widget and self.current_logic_widget in self.logic_rules:
            if messagebox.askyesno("Подтверждение", "Очистить все правила для этого виджета?"):
                del self.logic_rules[self.current_logic_widget]
                self.refresh_logic_display()
                self.logic_status.config(text="Все правила очищены", foreground="orange")

    def test_logic(self):
        """Тестирует логику в реальном времени"""
        if not self.current_logic_widget:
            messagebox.showinfo("Тест", "Выберите виджет для тестирования")
            return

        wo = next((w for w in self.widgets if str(w.id) == self.current_logic_widget), None)
        if not wo or not wo.widget_instance:
            messagebox.showerror("Ошибка", "Виджет не найден")
            return

        # Создаем тестовое окно
        test_win = tk.Toplevel(self.root)
        test_win.title(f"Тест логики - {wo.widget_type}")
        test_win.geometry("500x400")

        ttk.Label(test_win, text=f"Тестирование виджета: {wo.widget_type}",
                  font=("Arial", 12, "bold")).pack(pady=10)

        # Создаем копию виджета для теста
        test_frame = ttk.Frame(test_win)
        test_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=20)

        # Создаем тестовый виджет
        test_widget = self.create_test_widget(test_frame, wo)

        # Лог событий
        log_frame = ttk.LabelFrame(test_win, text="Лог событий", padding=5)
        log_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)

        log_text = tk.Text(log_frame, height=8, font=("Consolas", 9))
        log_text.pack(fill=tk.BOTH, expand=True)

        def log(message):
            log_text.insert(tk.END, f"{message}\n")
            log_text.see(tk.END)

        # Применяем правила
        if self.current_logic_widget in self.logic_rules:
            for rule in self.logic_rules[self.current_logic_widget]:
                self.apply_rule_to_test(test_widget, rule, log, test_frame)

        ttk.Button(test_win, text="Закрыть", command=test_win.destroy).pack(pady=10)

    def create_test_widget(self, parent, original):
        """Создает тестовую копию виджета"""
        wt = original.widget_type
        cfg = original.config.copy()

        # Создаем фрейм для виджета
        frame = tk.Frame(parent, bg=cfg.get("bg", "#f0f0f0"), relief=tk.RAISED, bd=2)
        frame.pack(pady=20)

        # Создаем сам виджет
        widget = None
        if wt == "Label":
            widget = tk.Label(frame, text=cfg.get("text", "Label"), bg=cfg.get("bg", "#f0f0f0"))
        elif wt == "Button":
            widget = tk.Button(frame, text=cfg.get("text", "Button"), bg=cfg.get("bg", "#e0e0e0"))
        elif wt == "Entry":
            widget = tk.Entry(frame, width=20)
            if cfg.get("text"):
                widget.insert(0, cfg["text"])
        else:
            widget = tk.Label(frame, text=f"[{wt}]", bg="lightyellow")

        widget.pack(padx=20, pady=20)
        return widget

    def apply_rule_to_test(self, widget, rule, log, parent):
        """Применяет правило к тестовому виджету"""
        event_map = {
            "click": "<Button-1>",
            "double_click": "<Double-Button-1>",
            "enter": "<Enter>",
            "leave": "<Leave>",
            "focus": "<FocusIn>",
            "blur": "<FocusOut>"
        }

        event = event_map.get(rule["event"], "<Button-1>")

        def handler(e):
            action = rule["action"]
            value = rule["value"]
            target_name = rule["target"]

            log(f"⚡ Событие: {rule['event']} → Действие: {action}")

            # Находим целевой виджет (упрощенно)
            if action == "set_text":
                if hasattr(widget, 'config'):
                    widget.config(text=value)
                    log(f"   ✓ Текст изменен на: {value}")
            elif action == "set_bg":
                if hasattr(widget, 'config'):
                    widget.config(bg=value)
                    log(f"   ✓ Фон изменен на: {value}")
            elif action == "show_hide":
                if value == "hide":
                    widget.pack_forget()
                    log(f"   ✓ Виджет скрыт")
                else:
                    widget.pack()
                    log(f"   ✓ Виджет показан")
            elif action == "set_value":
                if hasattr(widget, 'set'):
                    widget.set(value)
                    log(f"   ✓ Значение установлено: {value}")
            elif action == "call_function":
                try:
                    exec(value)
                    log(f"   ✓ Выполнен код: {value[:50]}")
                except Exception as e:
                    log(f"   ✗ Ошибка: {e}")

        widget.bind(event, handler)
        log(f"📌 Правило активировано: {rule['event']} → {rule['action']}")

    def save_logic(self):
        """Сохраняет логику в JSON"""
        if not self.logic_rules:
            messagebox.showinfo("Сохранение", "Нет правил для сохранения")
            return

        path = filedialog.asksaveasfilename(defaultextension=".logic.json",
                                            filetypes=[("Logic JSON", "*.logic.json")])
        if path:
            with open(path, "w", encoding="utf-8") as f:
                json.dump(self.logic_rules, f, ensure_ascii=False, indent=2)
            self.logic_status.config(text=f"Сохранено: {path}", foreground="green")

    def generate_logic_code(self):
        """Генерирует Python код на основе правил"""
        if not self.logic_rules:
            messagebox.showinfo("Генерация", "Нет правил для генерации")
            return

        lines = [
            "# Автоматически сгенерированная логика\n",
            "def _get_widget_val(w):\n",
            "    if w is None:\n",
            "        return ''\n",
            "    cls = w.winfo_class()\n",
            "    if cls in ('Text', 'TkText'):\n",
            "        return str(w.get('1.0', 'end-1c')).strip()\n",
            "    if hasattr(w, 'get') and callable(w.get):\n",
            "        try:\n",
            "            return str(w.get())\n",
            "        except Exception:\n",
            "            pass\n",
            "    if hasattr(w, 'cget'):\n",
            "        try:\n",
            "            return str(w.cget('text'))\n",
            "        except Exception:\n",
            "            pass\n",
            "    return ''\n",
            "\n",
        ]

        rule_idx = 0
        for widget_id, rules in self.logic_rules.items():
            wo = next((w for w in self.widgets if str(w.id) == widget_id), None)
            if not wo:
                continue

            widget_var = f"widget_{widget_id}"
            lines.append(f"# Логика для {wo.widget_type} (ID {widget_id})")

            for rule in rules:
                event = rule.get("event", "click")
                action = rule.get("action", "set_text")
                target = rule.get("target", "")
                value = rule.get("value", "")
                cond = (rule.get("condition") or "always").strip()
                aid = self.find_widget_id_by_name(rule.get("compare_a") or "", {})
                bid = self.find_widget_id_by_name(rule.get("compare_b") or "", {})

                event_map = {
                    "click": "<Button-1>",
                    "double_click": "<Double-Button-1>",
                    "enter": "<Enter>",
                    "leave": "<Leave>",
                    "focus": "<FocusIn>",
                    "blur": "<FocusOut>"
                }

                action_code = self.generate_action_code(action, target, value)
                inner_body = "\n".join(
                    "        " + ln.strip() if ln.strip() else ""
                    for ln in action_code.split("\n")
                )
                if cond in ("if_equal", "if_not_equal") and aid and bid:
                    op = "==" if cond == "if_equal" else "!="
                    inner_a = f"inner_{aid}"
                    inner_b = f"inner_{bid}"
                    guard = (
                        f"        # Условие: поля A (ID {aid}) и B (ID {bid}); "
                        f"подставьте {inner_a}, {inner_b} — внутренние виджеты\n"
                        f"        if not (_get_widget_val({inner_a}) {op} _get_widget_val({inner_b})):\n"
                        f"            return\n"
                    )
                    inner_body = guard + inner_body
                    lines.append(
                        f"# ID {aid} и {bid}: задайте {inner_a}, {inner_b} как первый дочерний виджет "
                        f"каждого контейнера на холсте\n"
                    )

                safe_event = str(event).replace("-", "_")
                fn = f"on_{safe_event}_{widget_id}_{rule_idx}"
                code = f"""
    def {fn}(event):
{inner_body}

    {widget_var}.bind('{event_map.get(event, "<Button-1>")}', {fn})
"""
                lines.append(code)
                rule_idx += 1

        code_window = tk.Toplevel(self.root)
        code_window.title("Сгенерированный код логики")
        code_window.geometry("700x500")

        text = tk.Text(code_window, font=("Consolas", 10))
        text.pack(fill=tk.BOTH, expand=True)
        text.insert("1.0", "\n".join(lines))
        text.config(state=tk.DISABLED)

        ttk.Button(code_window, text="📋 Копировать",
                   command=lambda: self.copy_to_clipboard("\n".join(lines))).pack(pady=5)

    def generate_action_code(self, action, target, value):
        """Генерирует код для действия"""
        if action == "set_text":
            return f"    {target}.config(text='{value}')"
        elif action == "set_bg":
            return f"    {target}.config(bg='{value}')"
        elif action == "show_hide":
            if value == "hide":
                return f"    {target}.pack_forget()"
            else:
                return f"    {target}.pack()"
        elif action == "set_value":
            return f"    {target}.set({value})"
        elif action == "call_function":
            return f"    {value}"
        return f"    pass"

    def copy_to_clipboard(self, text):
        """Копирует текст в буфер обмена"""
        self.root.clipboard_clear()
        self.root.clipboard_append(text)
        self.logic_status.config(text="Код скопирован ✓", foreground="green")
        self.root.after(2000, lambda: self.logic_status.config(text=""))
    def deselect_all(self):
        self.canvas.delete("selection")
        for wo in self.widgets:
            for h in wo.resize_handles: self.canvas.delete(h)
            wo.resize_handles=[]; wo.selection_rect=None
        self.selected_widgets=[]

    def draw_resize_handles(self, wo):
        for h in wo.resize_handles: self.canvas.delete(h)
        wo.resize_handles=[]
        x,y,w,h=wo.x,wo.y,wo.current_width,wo.current_height
        half=8
        pts=[(x,y),(x+w/2,y),(x+w,y),(x+w,y+h/2),(x+w,y+h),(x+w/2,y+h),(x,y+h),(x,y+h/2)]
        for hx,hy in pts:
            m=self.canvas.create_rectangle(hx-half,hy-half,hx+half,hy+half,
                fill="#1a6bff",outline="white",width=2,tags=("resize_handle",f"handle_{wo.id}"))
            wo.resize_handles.append(m)

    def _upd_sel_bounds(self, wo):
        if not wo.selection_rect: return
        x,y,w,h=wo.x,wo.y,wo.current_width,wo.current_height
        self.canvas.coords(wo.selection_rect, x-2,y-2,x+w+2,y+h+2)
        if wo.resize_handles:
            half=8
            pts=[(x,y),(x+w/2,y),(x+w,y),(x+w,y+h/2),(x+w,y+h),(x+w/2,y+h),(x,y+h),(x,y+h/2)]
            for i,h2 in enumerate(wo.resize_handles):
                if i<len(pts): hx,hy=pts[i]; self.canvas.coords(h2,hx-half,hy-half,hx+half,hy+half)

    # ── PROPERTIES ────────────────────────────────────────────────────────────
    def update_property(self, prop):
        if not self.selected_widgets: return
        val=self.prop_widgets[prop].get()
        for wid in self.selected_widgets:
            wo=next((w for w in self.widgets if str(w.id)==wid),None)
            if wo:
                if prop in ["width","height"]:
                    try: val=int(val)
                    except: pass
                wo.config[prop]=val
        for wid in self.selected_widgets:
            wo=next((w for w in self.widgets if str(w.id)==wid),None)
            if wo: self.render_widget(wo)
        self.undo_manager.save_state(f"Изменено {prop}")

    def choose_color(self, prop):
        c=colorchooser.askcolor()[1]
        if c:
            self.prop_widgets[prop].delete(0,tk.END); self.prop_widgets[prop].insert(0,c)
            self.update_property(prop)

    # ── LAYER PANEL ───────────────────────────────────────────────────────────
    def update_layer_panel(self):
        for c in self.layer_inner.winfo_children(): c.destroy()
        for wo in reversed(self.widgets):
            issel = str(wo.id) in self.selected_widgets
            rbg = "#ddeeff" if issel else ("white" if wo.visible else "#f5f5f5")
            row=tk.Frame(self.layer_inner,bg=rbg,pady=1)
            row.pack(fill=tk.X,padx=2,pady=1)
            tk.Button(row,text="👁" if wo.visible else "🚫",width=2,relief=tk.FLAT,
                      bg=rbg,bd=0,font=("Arial",9),
                      command=lambda o=wo: self._toggle_vis(o)).pack(side=tk.LEFT)
            tk.Button(row,text="🔒" if wo.locked else "🔓",width=2,relief=tk.FLAT,
                      bg=rbg,bd=0,font=("Arial",9),
                      command=lambda o=wo: self._toggle_lock(o)).pack(side=tk.LEFT)
            name=f"{ICONS.get(wo.widget_type,'')} {wo.widget_type}"
            fg="#aaa" if not wo.visible else ("black" if not wo.locked else "#888")
            lbl=tk.Label(row,text=name,anchor=tk.W,bg=rbg,fg=fg,font=("Arial",9))
            lbl.pack(side=tk.LEFT,fill=tk.X,expand=True,padx=4)
            for ww in [row,lbl]:
                ww.bind("<Button-1>",lambda e,o=wo: self._sel_layer(o))

    def _sel_layer(self, wo):
        self.deselect_all(); self.selected_widgets=[str(wo.id)]
        self.select_widgets(self.selected_widgets)

    def _toggle_vis(self, wo):
        wo.visible = not wo.visible
        if wo.visible:  self.render_widget(wo)
        else:
            if wo.widget_instance: self.canvas.delete(wo.widget_instance); wo.widget_instance=None
        self.update_layer_panel(); self.undo_manager.save_state("Видимость")

    def _toggle_lock(self, wo):
        wo.locked = not wo.locked; self.update_layer_panel()

    def _toggle_vis_sel(self):
        for wid in self.selected_widgets:
            wo=next((w for w in self.widgets if str(w.id)==wid),None)
            if wo: self._toggle_vis(wo)

    def _toggle_lock_sel(self):
        for wid in self.selected_widgets:
            wo=next((w for w in self.widgets if str(w.id)==wid),None)
            if wo: self._toggle_lock(wo)

    def move_layer_up(self):
        if not self.selected_widgets: return
        wid=self.selected_widgets[0]
        idx=next((i for i,w in enumerate(self.widgets) if str(w.id)==wid),None)
        if idx is not None and idx<len(self.widgets)-1:
            self.widgets[idx],self.widgets[idx+1]=self.widgets[idx+1],self.widgets[idx]
            self.update_layer_panel(); self.undo_manager.save_state("Слой ▲")

    def move_layer_down(self):
        if not self.selected_widgets: return
        wid=self.selected_widgets[0]
        idx=next((i for i,w in enumerate(self.widgets) if str(w.id)==wid),None)
        if idx is not None and idx>0:
            self.widgets[idx],self.widgets[idx-1]=self.widgets[idx-1],self.widgets[idx]
            self.update_layer_panel(); self.undo_manager.save_state("Слой ▼")

    # ── HISTORY PANEL ─────────────────────────────────────────────────────────
    def _refresh_history(self):
        for c in self.history_inner.winfo_children(): c.destroy()
        for i,(name,_) in enumerate(reversed(self.undo_manager.undo_stack)):
            latest=(i==0)
            bg="#e8f4fd" if latest else "white"
            prefix="● " if latest else f"{i+1}. "
            row=tk.Frame(self.history_inner,bg=bg)
            row.pack(fill=tk.X,pady=1,padx=2)
            tk.Label(row,text=f"{prefix}{name}",anchor=tk.W,bg=bg,
                     font=("Arial",8+(1 if latest else 0)),
                     fg="#1a6bff" if latest else "#333").pack(fill=tk.X,padx=4,pady=2)

    # ── OPERATIONS ────────────────────────────────────────────────────────────
    def delete_selected(self):
        if not self.selected_widgets: return
        for wid in self.selected_widgets[:]:
            wo=next((w for w in self.widgets if str(w.id)==wid),None)
            if wo:
                if wo.widget_instance: self.canvas.delete(wo.widget_instance)
                self.widgets.remove(wo)
        self.deselect_all(); self.update_layer_panel()
        self.undo_manager.save_state("Удаление"); self._update_minimap()
        self.update_canvas_scrollregion()

    def cut_selection(self):   self.copy_selection(); self.delete_selected()

    def copy_selection(self):
        if not self.selected_widgets: return
        self.clipboard=[]
        for wid in self.selected_widgets:
            wo=next((w for w in self.widgets if str(w.id)==wid),None)
            if wo: self.clipboard.append({"type":wo.widget_type,"x":wo.x,"y":wo.y,
                                           "config":wo.config.copy(),"events":wo.events.copy()})
        self.update_status(f"Скопировано {len(self.clipboard)}")

    def paste_selection(self):
        if not self.clipboard: return
        self.deselect_all()
        for item in self.clipboard:
            nw=WidgetItem(item["type"],item["x"]+20,item["y"]+20,item["config"].copy())
            nw.events=item["events"].copy()
            self.widgets.append(nw); self.render_widget(nw)
            self.selected_widgets.append(str(nw.id))
        self.select_widgets(self.selected_widgets); self.update_layer_panel()
        self.undo_manager.save_state("Вставка"); self._update_minimap()

    def _duplicate(self):
        self.copy_selection(); self.paste_selection()

    def _nudge(self, dx, dy):
        for wid in self.selected_widgets:
            wo=next((w for w in self.widgets if str(w.id)==wid),None)
            if wo and not wo.locked:
                wo.x+=dx; wo.y+=dy
                if wo.widget_instance:
                    self.canvas.coords(wo.widget_instance,wo.x,wo.y)
                self._upd_sel_bounds(wo)
        self._update_minimap()

    def bring_to_front(self):
        for wid in self.selected_widgets:
            wo=next((w for w in self.widgets if str(w.id)==wid),None)
            if wo and wo.widget_instance: self.canvas.tag_raise(wo.widget_instance)

    def send_to_back(self):
        for wid in self.selected_widgets:
            wo=next((w for w in self.widgets if str(w.id)==wid),None)
            if wo and wo.widget_instance:
                self.canvas.tag_lower(wo.widget_instance); self.canvas.tag_lower("grid")

    def group_selected(self):
        if len(self.selected_widgets)<2:
            messagebox.showinfo("Группировка","Выберите минимум 2 виджета"); return
        gid=f"group_{int(time.time())}"
        for wid in self.selected_widgets:
            wo=next((w for w in self.widgets if str(w.id)==wid),None)
            if wo: wo.group_id=gid
        self.undo_manager.save_state("Группировка")

    def ungroup_selected(self):
        cnt=0
        for wid in self.selected_widgets:
            wo=next((w for w in self.widgets if str(w.id)==wid),None)
            if wo and wo.group_id: wo.group_id=None; cnt+=1
        self.undo_manager.save_state("Разгруппировка")
        if not cnt: messagebox.showinfo("Разгруппировка","Нет сгруппированных")

    def show_context_menu(self, event):
        self.ctx.post(event.x_root, event.y_root)

    # ── TEMPLATES ─────────────────────────────────────────────────────────────
    def load_templates(self):
        for t in ["Форма входа","Форма регистрации","Dashboard","Калькулятор"]:
            self.template_listbox.insert(tk.END, t)

    def insert_template(self, event):
        sel=self.template_listbox.curselection()
        if not sel: return
        name=self.template_listbox.get(sel[0])
        if name=="Форма входа":        self._tpl_login()
        elif name=="Форма регистрации": self._tpl_register()
        elif name=="Dashboard":         self._tpl_dashboard()
        self.undo_manager.save_state(f"Шаблон: {name}")

    def _p(self, wt, x, y, cfg):
        nw=WidgetItem(wt,x,y,cfg); self.widgets.append(nw); self.render_widget(nw); return nw

    def _tpl_login(self):
        bx,by=80,80
        self._p("Label",bx,by,{"text":"Логин:","bg":"#f0f0f0","fg":"black","width":8,"height":1,"font":None})
        self._p("Entry",bx+90,by,{"text":"","bg":"white","fg":"black","width":14,"font":None})
        self._p("Label",bx,by+35,{"text":"Пароль:","bg":"#f0f0f0","fg":"black","width":8,"height":1,"font":None})
        self._p("Entry",bx+90,by+35,{"text":"","bg":"white","fg":"black","width":14,"font":None})
        self._p("Button",bx+60,by+75,{"text":"Войти","bg":"#4a90d9","fg":"white","width":10,"height":1,"font":None})
        self.update_layer_panel(); self._update_minimap()

    def _tpl_register(self):
        bx,by=80,50
        for lbl,dy in [("Имя:",0),("Email:",35),("Пароль:",70),("Повтор:",105)]:
            self._p("Label",bx,by+dy,{"text":lbl,"bg":"#f0f0f0","fg":"black","width":9,"height":1,"font":None})
            self._p("Entry",bx+100,by+dy,{"text":"","bg":"white","fg":"black","width":14,"font":None})
        self._p("Button",bx+50,by+145,{"text":"Зарегистрироваться","bg":"#27ae60","fg":"white","width":18,"height":1,"font":None})
        self.update_layer_panel(); self._update_minimap()

    def _tpl_dashboard(self):
        self._p("Label",20,20,{"text":"📊 Dashboard","bg":"#2c3e50","fg":"white","width":30,"height":2,"font":None})
        self._p("Frame",20,70,{"bg":"#ecf0f1","width":160,"height":80})
        self._p("Label",30,90,{"text":"Пользователи\n1 234","bg":"#ecf0f1","fg":"#2c3e50","width":12,"height":2,"font":None})
        self._p("Frame",195,70,{"bg":"#ecf0f1","width":160,"height":80})
        self._p("Label",205,90,{"text":"Заказы\n567","bg":"#ecf0f1","fg":"#2c3e50","width":12,"height":2,"font":None})
        self._p("Progressbar",20,165,{"value":65,"length":335,"mode":"determinate"})
        self._p("Label",20,190,{"text":"Выполнено: 65%","bg":"white","fg":"#555","width":20,"height":1,"font":None})
        self.update_layer_panel(); self._update_minimap()

    # ── AI (кнопки в верхней панели: 🔑 API, 🤖 ИИ: макет, 🤖 ИИ: экраны) ───────
    def open_ai_multi_screen_dialog(self):
        """Запрос описания и вызов генерации нескольких экранов."""
        p = simpledialog.askstring(
            "ИИ — многоэкранный интерфейс",
            "Опишите приложение (например: регистрация, вход, восстановление пароля):",
            parent=self.root,
        )
        if p and str(p).strip():
            self.ai_generate_multi_screen(str(p).strip())

    def open_ai_generate_dialog(self):
        """Окно с полем описания — генерация виджетов на текущий холст."""
        win = tk.Toplevel(self.root)
        win.title("🤖 ИИ — макет на холсте")
        win.geometry("540x340")
        win.transient(self.root)

        ttk.Label(
            win,
            text="Опишите интерфейс на русском или английском. Пример: «форма входа: email, пароль, кнопка Войти»",
            wraplength=500,
        ).pack(padx=12, pady=(12, 6), anchor=tk.W)

        txt = tk.Text(win, width=64, height=11, font=("Arial", 10), wrap=tk.WORD)
        txt.pack(fill=tk.BOTH, expand=True, padx=12, pady=8)

        bf = ttk.Frame(win)
        bf.pack(fill=tk.X, pady=(0, 12))

        def go():
            prompt = txt.get("1.0", "end-1c").strip()
            win.destroy()
            if prompt:
                self.ai_generate(prompt=prompt)

        ttk.Button(bf, text="Отмена", command=win.destroy).pack(side=tk.RIGHT, padx=6)
        ttk.Button(bf, text="Сгенерировать", command=go).pack(side=tk.RIGHT, padx=6)

    def ai_generate(self, prompt=None):
        """Генерация набора виджетов на текущий экран через DeepSeek (один холст)."""
        if prompt is None:
            self.open_ai_generate_dialog()
            return
        prompt = str(prompt).strip()
        if not prompt:
            return

        if not self.api_key:
            messagebox.showwarning(
                "API",
                "Сначала укажите ключ DeepSeek: верхняя панель → кнопка «🔑 API».",
            )
            return

        self.update_status("⏳ Генерирую через DeepSeek...")

        system_prompt = (
            "You are a Tkinter GUI layout assistant. Return ONLY valid JSON, no markdown fences. "
            "JSON format: {\"widgets\": [{\"type\": \"Label\", \"x\": 50, \"y\": 50, "
            "\"config\": {\"text\": \"Hello\", \"bg\": \"#f0f0f0\", \"fg\": \"black\"}}]}. "
            "Allowed types: Label Button Entry Checkbutton Radiobutton Listbox Text Scale Frame Spinbox Combobox Progressbar Separator Menubutton. "
            "Keep x within 50-550, y within 50-400."
        )

        try:
            result = self._call_deepseek_api(system_prompt, f"Create Tkinter GUI for: {prompt}")
            self._ai_apply(result, prompt_hint=prompt)
        except Exception as e:
            messagebox.showerror("Ошибка", f"DeepSeek ошибка: {str(e)}")
            self.update_status("❌ Ошибка генерации")

    def _ai_thread(self, prompt):
        sys_p=(
            "You are a Tkinter GUI layout assistant. Return ONLY valid JSON, no markdown fences. "
            "JSON format: {\"widgets\": [{\"type\": \"Label\", \"x\": 50, \"y\": 50, "
            "\"config\": {\"text\": \"Hello\", \"bg\": \"#f0f0f0\", \"fg\": \"black\", \"width\": 8, \"height\": 1, \"font\": null}}]}. "
            "Allowed types: Label Button Entry Checkbutton Radiobutton Listbox Text Scale Frame Spinbox Combobox Progressbar Separator Menubutton. "
            "Keep x within 50-550, y within 50-400. Create realistic compact layouts."
        )
        body=json.dumps({
            "model":"claude-sonnet-4-20250514","max_tokens":1200,
            "system":sys_p,
            "messages":[{"role":"user","content":f"Create Tkinter GUI for: {prompt}"}]
        }).encode()
        try:
            req=urllib.request.Request(
                "https://api.anthropic.com/v1/messages", data=body,
                headers={"Content-Type":"application/json","x-api-key":self.api_key,
                         "anthropic-version":"2023-06-01"}, method="POST")
            with urllib.request.urlopen(req, timeout=30) as resp:
                res=json.loads(resp.read().decode())
                text=res["content"][0]["text"]
                self.root.after(0, lambda t=text, pr=prompt: self._ai_apply(t, prompt_hint=pr))
        except urllib.error.HTTPError as e:
            msg=e.read().decode()
            self.root.after(0, lambda: messagebox.showerror("AI Error",f"{e.code}: {msg[:300]}"))
            self.root.after(0, lambda: self.update_status(f"AI ошибка {e.code}"))
        except Exception as e:
            self.root.after(0, lambda: messagebox.showerror("AI Error",str(e)))
            self.root.after(0, lambda: self.update_status("AI ошибка"))

    def _ai_apply(self, text, prompt_hint=""):
        try:
            t=text.strip()
            if "```" in t:
                t=t.split("```")[1]
                if t.startswith("json"): t=t[4:]
            data=json.loads(t)
            items=data.get("widgets",data) if isinstance(data,dict) else data
            cnt=0
            for item in items:
                wt=item.get("type","Label")
                if wt not in ICONS: continue
                cfg=item.get("config",{})
                if not isinstance(cfg,dict): cfg={}
                nw=WidgetItem(wt,item.get("x",50),item.get("y",50),cfg)
                self.widgets.append(nw); self.render_widget(nw); cnt+=1
            self.update_layer_panel(); self._update_minimap()
            hint = (prompt_hint or "")[:25]
            self.undo_manager.save_state(f"AI: {hint}")
            self.update_status(f"AI создал {cnt} виджетов ✓")
        except Exception as e:
            messagebox.showerror("AI Parse Error",f"{e}\n\n{text[:300]}")
            self.update_status("AI: ошибка парсинга")

    # ── SMART PREVIEW ─────────────────────────────────────────────────────────
    def preview(self):
        """Предпросмотр с поддержкой экранов"""
        if self.screens:
            self.preview_with_screens()
        else:
            # Предпросмотр с логикой + панель ИИ
            win = tk.Toplevel(self.root)
            win.title("👁 Предпросмотр + ИИ")
            win.geometry("900x720")
            win.configure(bg="white")

            screen_state = {"name": None}

            pw = ttk.PanedWindow(win, orient=tk.VERTICAL)
            pw.pack(fill=tk.BOTH, expand=True, padx=6, pady=6)

            upper = ttk.Frame(pw)
            pw.add(upper, weight=2)

            cv = tk.Canvas(upper, bg="white", highlightthickness=0)
            cv.pack(fill=tk.BOTH, expand=True, padx=4, pady=4)

            preview_widgets = {}
            for wo in self.widgets:
                if not wo.visible:
                    continue

                cfg = wo.config
                wt = wo.widget_type

                try:
                    w = self.create_preview_widget(cv, wt, cfg, wo)
                    cid = cv.create_window(wo.x, wo.y, window=w, anchor="nw")
                    preview_widgets[str(wo.id)] = {
                        "widget": w,
                        "canvas_id": cid,
                        "x": wo.x,
                        "y": wo.y,
                    }
                except Exception:
                    pass

            if self.logic_rules and preview_widgets:
                self.apply_logic_to_preview(preview_widgets, cv)

            lower = ttk.Frame(pw)
            pw.add(lower, weight=1)
            self.attach_preview_ai_panel(win, screen_state, parent=lower)

    def create_preview_widget(self, parent, wt, cfg, original_wo):
        """Создает виджет для предпросмотра"""
        # Определяем размеры
        width = original_wo.current_width
        height = original_wo.current_height

        if wt in ["Label", "Button", "Checkbutton", "Radiobutton", "Menubutton"]:
            w = tk.Frame(parent, width=width, height=height, bg=cfg.get("bg", "#f0f0f0"))
            w.pack_propagate(False)

            if wt == "Label":
                inner = tk.Label(w, text=cfg.get("text", "Label"), bg=cfg.get("bg", "#f0f0f0"),
                                 fg=cfg.get("fg", "black"), font=cfg.get("font"))
            elif wt == "Button":
                inner = tk.Button(w, text=cfg.get("text", "Button"), bg=cfg.get("bg", "#e0e0e0"),
                                  fg=cfg.get("fg", "black"), font=cfg.get("font"))
            elif wt == "Checkbutton":
                inner = tk.Checkbutton(w, text=cfg.get("text", "Check"), bg=cfg.get("bg", "#f0f0f0"),
                                       fg=cfg.get("fg", "black"), font=cfg.get("font"))
            elif wt == "Radiobutton":
                inner = tk.Radiobutton(w, text=cfg.get("text", "Radio"), bg=cfg.get("bg", "#f0f0f0"),
                                       fg=cfg.get("fg", "black"), font=cfg.get("font"))
            else:  # Menubutton
                inner = tk.Menubutton(w, text=cfg.get("text", "Меню"), bg=cfg.get("bg", "#e0e0e0"),
                                      fg=cfg.get("fg", "black"), relief=tk.RAISED)
                if original_wo.config.get("menu_items"):
                    menu = tk.Menu(inner, tearoff=0)
                    for item in original_wo.config["menu_items"].split("\n"):
                        if item.strip() == "---":
                            menu.add_separator()
                        elif item.strip():
                            menu.add_command(label=item.strip())
                    inner["menu"] = menu

            inner.pack(fill=tk.BOTH, expand=True)
            return w

        elif wt == "Entry":
            w = tk.Frame(parent, width=width, height=height)
            w.pack_propagate(False)
            inner = tk.Entry(w, width=cfg.get("width", 12), bg=cfg.get("bg", "white"),
                             fg=cfg.get("fg", "black"), font=cfg.get("font"))
            if cfg.get("text"):
                inner.insert(0, cfg["text"])
            if cfg.get("state") == "readonly":
                inner.config(state="readonly")
            inner.pack(fill=tk.BOTH, expand=True)
            return w

        elif wt == "Text":
            w = tk.Frame(parent, width=width, height=height)
            w.pack_propagate(False)
            inner = tk.Text(w, width=cfg.get("width", 20), height=cfg.get("height", 3),
                            bg=cfg.get("bg", "white"), fg=cfg.get("fg", "black"),
                            font=cfg.get("font"), wrap=cfg.get("wrap", "word"))
            inner.pack(fill=tk.BOTH, expand=True)
            return w

        elif wt == "Spinbox":
            w = tk.Frame(parent, width=width, height=height)
            w.pack_propagate(False)
            inner = ttk.Spinbox(w, from_=cfg.get("from_", 0), to=cfg.get("to", 100),
                                width=cfg.get("width", 8))
            inner.pack(fill=tk.BOTH, expand=True)
            return w

        elif wt == "Combobox":
            w = tk.Frame(parent, width=width, height=height)
            w.pack_propagate(False)
            vals = [v.strip() for v in str(cfg.get("values", "")).split(",") if v.strip()]
            inner = ttk.Combobox(w, values=vals, width=cfg.get("width", 12))
            if vals:
                inner.set(vals[0])
            inner.pack(fill=tk.BOTH, expand=True)
            return w

        elif wt == "Listbox":
            w = tk.Frame(parent, width=width, height=height)
            w.pack_propagate(False)
            inner = tk.Listbox(w, width=cfg.get("width", 12), height=cfg.get("height", 4),
                               bg=cfg.get("bg", "white"), fg=cfg.get("fg", "black"),
                               font=cfg.get("font"))
            # Добавляем пример элементов
            for i in range(5):
                inner.insert(tk.END, f"Элемент {i + 1}")
            inner.pack(fill=tk.BOTH, expand=True)
            return w

        elif wt == "Scale":
            w = tk.Frame(parent, width=width, height=height)
            w.pack_propagate(False)
            orient = tk.HORIZONTAL if cfg.get("orient", "horizontal") == "horizontal" else tk.VERTICAL
            inner = tk.Scale(w, orient=orient, from_=cfg.get("from_", 0), to=cfg.get("to", 100),
                             length=cfg.get("length", 150))
            inner.pack(fill=tk.BOTH, expand=True)
            return w

        elif wt == "Progressbar":
            w = tk.Frame(parent, width=width, height=height)
            w.pack_propagate(False)
            inner = ttk.Progressbar(w, mode=cfg.get("mode", "determinate"),
                                    value=cfg.get("value", 50), length=cfg.get("length", 120))
            inner.pack(fill=tk.BOTH, expand=True)
            return w

        elif wt in ["Frame", "Canvas"]:
            w = tk.Frame(parent, width=width, height=height, bg=cfg.get("bg", "#e8e8e8"),
                         relief=tk.GROOVE, bd=1)
            w.pack_propagate(False)
            tk.Label(w, text=f"[{wt}]", bg=cfg.get("bg", "#e8e8e8"), fg="#888").place(relx=.5, rely=.5, anchor="center")
            return w

        else:
            # fallback
            w = tk.Frame(parent, width=width, height=height, bg="lightyellow", relief=tk.RAISED, bd=1)
            w.pack_propagate(False)
            tk.Label(w, text=f"? {wt}", bg="lightyellow").pack(expand=True)
            return w

    def apply_logic_to_preview(self, preview_widgets, canvas):
        """Применяет все правила логики к виджетам в предпросмотре"""
        log_entries = []  # Для сбора логов

        event_map = {
            "click": "<Button-1>",
            "double_click": "<Double-Button-1>",
            "enter": "<Enter>",
            "leave": "<Leave>",
            "focus": "<FocusIn>",
            "blur": "<FocusOut>",
            "key_press": "<KeyRelease>",
        }

        for widget_id, rules in self.logic_rules.items():
            if widget_id not in preview_widgets:
                continue

            source_widget_data = preview_widgets[widget_id]
            source_widget = source_widget_data["widget"]

            # Получаем внутренний виджет (первый дочерний элемент)
            inner_widget = None
            for child in source_widget.winfo_children():
                inner_widget = child
                break

            if not inner_widget:
                continue

            # Несколько правил на одно событие: bind(..., add='+')
            event_bind_count = {}

            for rule in rules:
                ev = rule.get("event", "click")
                tk_ev = event_map.get(ev, "<Button-1>")
                n = event_bind_count.get(tk_ev, 0)
                event_bind_count[tk_ev] = n + 1
                self.bind_preview_event(
                    inner_widget, rule, preview_widgets, log_entries, canvas,
                    bind_add=(n > 0),
                )

        # Если есть логи, показываем в консоли
        if log_entries:
            print("=== Логика в предпросмотре ===")
            for log in log_entries:
                print(log)

    def find_widget_id_by_name(self, target_name, preview_widgets):
        """Находит ID виджета по имени"""
        # Ищем по формату "Button (ID: 12345678)"
        import re
        match = re.search(r'ID: (\d+)', target_name)
        if match:
            return match.group(1)
        return None

    def _preview_inner_widget(self, preview_widgets, widget_id):
        """Первый дочерний виджет в контейнере предпросмотра."""
        if not widget_id or widget_id not in preview_widgets:
            return None
        tw = preview_widgets[widget_id]["widget"]
        for child in tw.winfo_children():
            return child
        return None

    def _widget_value_for_compare(self, inner):
        """Текст/значение виджета для сравнения (Entry, Label, Text, …)."""
        if inner is None:
            return ""
        cls = inner.winfo_class()
        if cls in ("Text", "TkText"):
            try:
                return str(inner.get("1.0", "end-1c")).strip()
            except Exception:
                return ""
        if hasattr(inner, "get") and callable(inner.get):
            try:
                return str(inner.get())
            except (tk.TclError, Exception):
                pass
        if hasattr(inner, "cget"):
            try:
                return str(inner.cget("text"))
            except Exception:
                pass
        return ""

    def _evaluate_rule_condition(self, rule, preview_widgets):
        """Проверка условия правила (в т.ч. поле A == поле B)."""
        cond = (rule.get("condition") or "always").strip()
        if cond in ("", "always", "none"):
            return True
        a_name = rule.get("compare_a") or ""
        b_name = rule.get("compare_b") or ""
        aid = self.find_widget_id_by_name(a_name, preview_widgets)
        bid = self.find_widget_id_by_name(b_name, preview_widgets)
        if not aid or not bid:
            return False
        inner_a = self._preview_inner_widget(preview_widgets, aid)
        inner_b = self._preview_inner_widget(preview_widgets, bid)
        va = self._widget_value_for_compare(inner_a)
        vb = self._widget_value_for_compare(inner_b)
        if cond == "if_equal":
            return va == vb
        if cond == "if_not_equal":
            return va != vb
        return True

    def bind_preview_event(self, widget, rule, preview_widgets, log_entries, canvas, bind_add=False):
        """Привязывает событие к виджету в предпросмотре"""
        event = rule.get("event", "click")
        action = rule.get("action", "set_text")
        target_id = self.find_widget_id_by_name(rule.get("target", ""), preview_widgets)
        value = rule.get("value", "")

        event_map = {
            "click": "<Button-1>",
            "double_click": "<Double-Button-1>",
            "enter": "<Enter>",
            "leave": "<Leave>",
            "focus": "<FocusIn>",
            "blur": "<FocusOut>",
            "key_press": "<KeyRelease>",
        }

        tk_event = event_map.get(event, "<Button-1>")

        def handler(e):
            if not self._evaluate_rule_condition(rule, preview_widgets):
                log_msg = f"⚡ {event} → условие не выполнено (A/B), действие пропущено"
                log_entries.append(log_msg)
                print(log_msg)
                return

            # Находим целевой виджет
            target_widget_data = None
            target_inner = None

            if target_id and target_id in preview_widgets:
                target_widget_data = preview_widgets[target_id]
                target_widget = target_widget_data["widget"]
                # Получаем внутренний виджет
                for child in target_widget.winfo_children():
                    target_inner = child
                    break

            # Выполняем действие
            log_msg = f"⚡ {event} → {action}"

            try:
                if action == "set_text":
                    if target_inner and hasattr(target_inner, 'config'):
                        target_inner.config(text=value)
                        log_msg += f" (текст: {value})"

                elif action == "set_bg":
                    if target_inner and hasattr(target_inner, 'config'):
                        target_inner.config(bg=value)
                        # Также меняем фон контейнера
                        if target_widget_data:
                            target_widget_data["widget"].config(bg=value)
                        log_msg += f" (фон: {value})"

                elif action == "show_hide":
                    if target_widget_data:
                        if value == "hide":
                            canvas.itemconfig(target_widget_data["canvas_id"], state='hidden')
                            log_msg += " (скрыт)"
                        else:
                            canvas.itemconfig(target_widget_data["canvas_id"], state='normal')
                            log_msg += " (показан)"

                elif action == "enable_disable":
                    if target_inner:
                        if value == "disable":
                            target_inner.config(state='disabled')
                            log_msg += " (отключен)"
                        else:
                            target_inner.config(state='normal')
                            log_msg += " (включен)"

                elif action == "set_value":
                    if target_inner and hasattr(target_inner, 'set'):
                        target_inner.set(value)
                        log_msg += f" (значение: {value})"
                    elif target_inner and hasattr(target_inner, 'config'):
                        target_inner.config(value=value)
                        log_msg += f" (значение: {value})"

                elif action == "call_function":
                    # Безопасное выполнение кода
                    try:
                        exec(value, {"widget": target_inner, "value": value})
                        log_msg += f" (выполнен код)"
                    except Exception as ex:
                        log_msg += f" (ошибка: {ex})"

                log_entries.append(log_msg)
                print(log_msg)

                # Обновляем холст
                canvas.update_idletasks()

            except Exception as ex:
                error_msg = f"❌ Ошибка: {ex}"
                log_entries.append(error_msg)
                print(error_msg)

        if bind_add:
            widget.bind(tk_event, handler, add="+")
        else:
            widget.bind(tk_event, handler)

    def make_preview_draggable(self, preview_widgets, canvas):
        """Делает виджеты в предпросмотре перетаскиваемыми (опционально)"""
        drag_data = {"x": 0, "y": 0, "item": None, "widget_id": None}

        def on_press(event, widget_id, canvas_id):
            drag_data["x"] = event.x
            drag_data["y"] = event.y
            drag_data["item"] = canvas_id
            drag_data["widget_id"] = widget_id

        def on_drag(event):
            if drag_data["item"]:
                dx = event.x - drag_data["x"]
                dy = event.y - drag_data["y"]
                canvas.move(drag_data["item"], dx, dy)
                drag_data["x"] = event.x
                drag_data["y"] = event.y

                # Обновляем координаты в данных
                if drag_data["widget_id"] in preview_widgets:
                    coords = canvas.coords(drag_data["item"])
                    if coords:
                        preview_widgets[drag_data["widget_id"]]["x"] = coords[0]
                        preview_widgets[drag_data["widget_id"]]["y"] = coords[1]

        for widget_id, data in preview_widgets.items():
            widget = data["widget"]
            canvas_id = data["canvas_id"]

            widget.bind("<Button-1>", lambda e, wid=widget_id, cid=canvas_id: on_press(e, wid, cid))
            widget.bind("<B1-Motion>", on_drag)

    def refresh_preview(self, window):
        """Обновляет предпросмотр"""
        for child in window.winfo_children():
            if isinstance(child, tk.Canvas):
                child.destroy()
        # Пересоздаем предпросмотр
        self.preview()

    def show_preview_logs(self, window):
        """Показывает окно с логами предпросмотра"""
        log_win = tk.Toplevel(window)
        log_win.title("Логи предпросмотра")
        log_win.geometry("500x300")

        text = tk.Text(log_win, font=("Consolas", 9))
        text.pack(fill=tk.BOTH, expand=True)

        # Здесь можно собирать реальные логи
        text.insert(tk.END, "Логи будут появляться здесь при взаимодействии\n")
        text.config(state=tk.DISABLED)

    # ── CODE ──────────────────────────────────────────────────────────────────
    def generate_code(self):
        lines=["import tkinter as tk","from tkinter import ttk","",
               "class GeneratedApp:","    def __init__(self, root):",
               "        self.root = root","        self.root.title('Generated App')",
               "        self.root.geometry('800x600')",""]
        TTK_TYPES={"Spinbox","Combobox","Progressbar","Separator","Notebook","PanedWindow"}
        for wo in self.widgets:
            if not wo.visible: continue
            var=f"self.{wo.widget_type.lower()}_{str(wo.id)[-4:]}"
            parts=[f'{k}="{v}"' if isinstance(v,str) else f'{k}={v}'
                   for k,v in wo.config.items() if v is not None and v!=""]
            ns = "ttk" if wo.widget_type in TTK_TYPES else "tk"
            lines.append(f"        {var} = {ns}.{wo.widget_type}(self.root, {', '.join(parts)})")
            lines.append(f"        {var}.place(x={int(wo.x)}, y={int(wo.y)})")
            for ev,fn in wo.events.items():
                if fn: lines.append(f"        {var}.bind('{ev}', self.{fn})")
            lines.append("")
        lines+=["","if __name__ == '__main__':","    root = tk.Tk()","    app = GeneratedApp(root)","    root.mainloop()"]
        code="\n".join(lines)

        top=tk.Toplevel(self.root); top.title("🐍 Код"); top.geometry("720x520")
        txt=tk.Text(top,font=("Consolas",10),wrap=tk.NONE)
        txt.pack(fill=tk.BOTH,expand=True); txt.insert(tk.END,code); txt.config(state=tk.DISABLED)
        bf=ttk.Frame(top); bf.pack(fill=tk.X,pady=4)

        def _copy():
            self.root.clipboard_clear(); self.root.clipboard_append(code)
            self.update_status("Код скопирован ✓")

        def _save():
            path=filedialog.asksaveasfilename(defaultextension=".py",filetypes=[("Python","*.py")])
            if path:
                with open(path,"w",encoding="utf-8") as f: f.write(code)
                self.update_status(f"Сохранено: {path}")

        ttk.Button(bf,text="📋 Копировать",command=_copy).pack(side=tk.LEFT,padx=8)
        ttk.Button(bf,text="💾 Сохранить .py",command=_save).pack(side=tk.LEFT,padx=4)
        ttk.Button(bf,text="✕ Закрыть",command=top.destroy).pack(side=tk.RIGHT,padx=8)

    # ── SAVE / LOAD ───────────────────────────────────────────────────────────
    def save_project(self):
        data=[{"type":wo.widget_type,"x":wo.x,"y":wo.y,"config":wo.config,"events":wo.events,
               "visible":wo.visible,"locked":wo.locked,"group_id":wo.group_id}
              for wo in self.widgets]
        path=filedialog.asksaveasfilename(defaultextension=".json",filetypes=[("JSON","*.json")])
        if path:
            with open(path,"w",encoding="utf-8") as f: json.dump(data,f,ensure_ascii=False,indent=2)
            self.update_status(f"Сохранено ✓")

    def load_project(self):
        path=filedialog.askopenfilename(filetypes=[("JSON","*.json")])
        if not path: return
        try:
            with open(path,"r",encoding="utf-8") as f: data=json.load(f)
            self.canvas.delete("all"); self.widgets=[]; self.deselect_all()
            for item in data:
                wo=WidgetItem(item["type"],item["x"],item["y"],item["config"])
                wo.events=item.get("events",{}); wo.visible=item.get("visible",True)
                wo.locked=item.get("locked",False); wo.group_id=item.get("group_id",None)
                self.widgets.append(wo); self.render_widget(wo)
            self.draw_grid(); self.update_layer_panel(); self._update_minimap()
            self.update_status(f"Загружено ✓")
        except Exception as e:
            messagebox.showerror("Ошибка",str(e))

    def restore_state(self, state):
        self.canvas.delete("all"); self.widgets=[]
        data=state.get("widgets",state) if isinstance(state,dict) else state
        self.current_container_id=state.get("current_container") if isinstance(state,dict) else None
        for item in data:
            wo=WidgetItem(item["type"],item["x"],item["y"],item["config"])
            wo.events=item.get("events",{}); wo.parent_id=item.get("parent_id",None)
            wo.group_id=item.get("group_id",None); wo.visible=item.get("visible",True)
            wo.locked=item.get("locked",False)
            self.widgets.append(wo); self.render_widget(wo)
        self.draw_grid(); self.update_layer_panel(); self.deselect_all(); self._update_minimap()

    def update_status(self, msg):
        self.status_label.config(text=msg)

    # compat shims
    def update_tree(self): self.update_layer_panel()
    def filter_widgets(self,q): pass


# ─────────────────────────────────────────────────────────────────────────────
def main():
    root = tk.Tk()
    GUIBuilderApp(root)
    root.mainloop()

if __name__ == "__main__":
    main()