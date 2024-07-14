/*
 * Copyright 2014 Google Inc.
 *
 * Use of this source code is governed by a BSD-style license that can be
 * found in the LICENSE file.
 */

// running create_test_font_color generates ./<cbdt|sbix|cpal>.ttx
// which are read by fonttools ttx to produce native fonts.

#include "src/base/SkAutoMalloc.h"
#include "include/core/SkRefCnt.h"
#include "include/core/SkStream.h"
#include "include/core/SkString.h"
#include "include/core/SkCanvas.h"
#include "include/core/SkFontMgr.h"
#include "include/core/SkSurface.h"
#include "include/core/SkFont.h"
#include "include/core/SkFontStyle.h"
#include "include/core/SkColorSpace.h"
#include "include/core/SkTextBlob.h"
#include "include/core/SkBitmap.h"
#include "tools/flags/CommandLineFlags.h"
#include "tools/fonts/TestSVGTypeface.h"
#include "tools/window/RasterWindowContext.h"
#include "tools/fonts/FontToolUtils.h"
#include "modules/skparagraph/src/ParagraphBuilderImpl.h"
#include "modules/skparagraph/src/Run.h"
#include "modules/skparagraph/src/TextWrapper.h"
#include "modules/skparagraph/src/ParagraphImpl.h"
#include "modules/skparagraph/include/FontCollection.h"
#include "modules/skparagraph/include/ParagraphStyle.h"
#include "modules/skparagraph/include/Paragraph.h"
#include "modules/skparagraph/include/TextStyle.h"
#include "Windows.h"
#include <cmath>
#include <cassert>

#pragma comment(lib, "skparagraph")

#if defined(SK_ENABLE_SVG)

#define ArrayCount(a) sizeof((a)) / sizeof(*(a))

#define Halt __debugbreak();

#define Pre(a) \
    if (!(a)) Halt
#define Post(a) \
    if (!(a)) Halt
#define Invariant(a) \
    if (!(a)) Halt
#define Implies(a, b) (!(a) || (b))
#define Iff(a, b) ((a) == (b))

static void drawTextWithSoftHyphen(SkCanvas* canvas,
                            const char* text,
                            float x,
                            float y,
                            const SkPaint& paint,
                            const SkFont& font);

static void DebugMessage(const char* format, ...) 
{
    char Temp[1024];
    va_list Args;
    va_start(Args, format);
    wvsprintfA(Temp, format, Args);
    va_end(Args);
    OutputDebugStringA(Temp);
}

struct FiberData 
{
    void* mainFiber;
    void* msgFiber;
    HWND window;
    bool isQuit;
};

static SkAutoMalloc globalSurfaceMemory;
const char* g_sWindowClass = "FirstSkiaApp";

LRESULT CALLBACK WndProc(HWND hWnd, UINT message, WPARAM wParam, LPARAM lParam);
static HWND MakeWindow(int w, int h)
{
    HWND result;
    static WNDCLASSEX wcex;
    static bool wcexInit = false;

    if (!wcexInit) {
        wcex.cbSize = sizeof(WNDCLASSEX);

        wcex.style = CS_HREDRAW | CS_VREDRAW | CS_OWNDC;
        wcex.lpfnWndProc = WndProc;
        wcex.cbClsExtra = 0;
        wcex.cbWndExtra = 0;
        wcex.hInstance = GetModuleHandle(nullptr);
        wcex.hIcon = LoadIcon(wcex.hInstance, (LPCTSTR)IDI_WINLOGO);
        wcex.hCursor = LoadCursor(nullptr, IDC_ARROW);
        wcex.lpszMenuName = nullptr;
        wcex.lpszClassName = g_sWindowClass;
        wcex.hIconSm = LoadIcon(wcex.hInstance, (LPCTSTR)IDI_WINLOGO);

        if (RegisterClassEx(&wcex)) wcexInit = true;
    }

    result = CreateWindow(g_sWindowClass,
                          nullptr,
                          WS_OVERLAPPEDWINDOW,
                          0,
                          0,
                          w,
                          h,
                          nullptr,
                          nullptr,
                          wcex.hInstance,
                          nullptr);

    return result;
}

static auto ResizeFrameBuffer(int w, int h) 
{
    const size_t bmpSize = sizeof(BITMAPINFOHEADER) + (h * (w * sizeof(uint32_t)));
    globalSurfaceMemory.reset(bmpSize);
    BITMAPINFO* bmpInfo = reinterpret_cast<BITMAPINFO*>(globalSurfaceMemory.get());
    ZeroMemory(globalSurfaceMemory.get(), bmpSize);
    bmpInfo->bmiHeader.biSize = sizeof(BITMAPINFOHEADER);
    bmpInfo->bmiHeader.biWidth = w;
    bmpInfo->bmiHeader.biHeight = -h; // negative means top-down bitmap. Skia draws top-down.
    bmpInfo->bmiHeader.biPlanes = 1;
    bmpInfo->bmiHeader.biBitCount = 32;
    bmpInfo->bmiHeader.biCompression = BI_RGB;
    SkImageInfo info = SkImageInfo::Make(w, h, kBGRA_8888_SkColorType, kPremul_SkAlphaType);

    return SkCanvas::MakeRasterDirect(info, bmpInfo->bmiColors, w * sizeof(uint32_t));
}

static void SwapFrameBuffers(HWND window) 
{
    BITMAPINFO* bmpInfo = reinterpret_cast<BITMAPINFO*>(globalSurfaceMemory.get());
    HDC dc = GetDC(window);
    if (dc == 0) return;
	StretchDIBits(dc, 0, 0, 
                  bmpInfo->bmiHeader.biWidth, 
                  -bmpInfo->bmiHeader.biHeight, 
                  0, 0,
                  bmpInfo->bmiHeader.biWidth,
                  -bmpInfo->bmiHeader.biHeight,
                  bmpInfo->bmiColors,
		          bmpInfo, DIB_RGB_COLORS, SRCCOPY);
    ReleaseDC(window, dc);
}

static const char* MaxStr(const char** texts, size_t count) 
{ 
    if (count == 0 || !texts) 
        return nullptr;

    const char* result = texts[0];
    for (size_t i = 0; i < count; ++i)
        result = strlen(result) < strlen(texts[i]) ? texts[i] : result;

    return result; 
}


static void DrawColor(SkCanvas* canvas, SkColor4f color) 
{
    canvas->clear(color);
}

static void ClearFrameBuffers(SkCanvas* canvas, SkColor4f color) 
{
    DrawColor(canvas, color);
}

struct Area 
{
    int width;
    int height;
};

static Area GetClientWindowArea(HWND window) 
{
    Area result = {};

    RECT clientRectangle = {};
    GetClientRect(window, &clientRectangle);

    int width = clientRectangle.right - clientRectangle.left;
    int height = clientRectangle.bottom - clientRectangle.top;

    result.width = width;
    result.height = height;

    return result;
}

static void CALLBACK FiberMessageProc(FiberData* data) 
{ 
    for (;;) 
    {
        MSG message;
        while (PeekMessage(&message, 0, 0, 0, PM_REMOVE))
        {
			TranslateMessage(&message);
			DispatchMessage(&message);
        }
        SwitchToFiber(data->mainFiber);
    }
}

static void PullFiberState(FiberData* data) 
{ 
    SwitchToFiber(data->msgFiber); 
}

static void PushFiberState(FiberData* data) 
{
}
LRESULT CALLBACK WndProc(HWND window, UINT message, WPARAM wParam, LPARAM lParam)
{
    FiberData* data = (FiberData*)GetWindowLongPtr(window, GWLP_USERDATA);

    LRESULT result = 0;

	switch (message)
	{
    case WM_TIMER:
        SwitchToFiber(data->mainFiber);
        break;
    case WM_ENTERMENULOOP:
    case WM_ENTERSIZEMOVE:
        assert(data->window == window);
        SetTimer(window, 1, 1, 0);
        break;
    case WM_EXITMENULOOP:
    case WM_EXITSIZEMOVE:
        assert(data->window == window);
        KillTimer(window, 1);
        break;
	case WM_PAINT:
	{
		PAINTSTRUCT ps;
		auto hdc = BeginPaint(window, &ps);
        assert(data->window == window);
		EndPaint(window, &ps);
        break;
	}
    case WM_SIZE: 
    {
        UINT width = LOWORD(lParam);
        UINT height = HIWORD(lParam);

        if (width > 0 && height > 0) 
        {
            auto canvas = ResizeFrameBuffer(width, height);
            ClearFrameBuffers(canvas.get(), SkColors::kLtGray);
        }
        break;
    }

    case WM_DESTROY:
		PostQuitMessage(0);
        data->isQuit = true;
		break;

	case WM_CLOSE:
        assert(data->window == window);
		DestroyWindow(window);
        data->isQuit = true;
		break;

	default: 
        result = DefWindowProc(window, message, wParam, lParam);
	}

	return result;
}

static void drawTextWithSoftHyphen(SkCanvas* canvas,
                            const char* text,
                            float x,
                            float y,
                            const SkPaint& paint,
                            const SkFont& font) 
{
    SkTextBlobBuilder builder{};
    const char* current = text;
    float currentX = x;

    // Allocate a buffer for the maximum possible glyphs
    size_t maxGlyphs = strlen(text);
    std::vector<SkGlyphID> glyphs(maxGlyphs);

    while (*current) 
    {
        // Find the next soft hyphen (utf8: 0xC2 0xAD)
        const char* start = strchr(current, '\xC2');
        // No more soft hyphens, draw the rest of the text.
        if (!start) 
        {
            size_t postHyphenGlyphCount = maxGlyphs - (current - text);
            // Convert post-hyphen text to glyphs
            int glyphCount = font.textToGlyphs(current,
                                               postHyphenGlyphCount,
                                               SkTextEncoding::kUTF8,
                                               glyphs.data(),
                                               glyphs.size());
            const SkTextBlobBuilder::RunBuffer& buffer = builder.allocRun(font, glyphCount, currentX, y);
            // Copy the glyph indexes
            memcpy(buffer.glyphs, glyphs.data(), glyphCount * sizeof(SkGlyphID));
            // Draw the rest of the text
            sk_sp<SkTextBlob> blob = builder.make();
            canvas->drawTextBlob(blob, 0, 0, paint);
            return;
        }
        //const char* end = strchr(start, '\xAD');
        const char* end = start + 1;
        assert(*end == '\xAD');

        const size_t preHyphenGlyphCount = start - current;

        // Convert pre-hyphen text to glyphs
        int glyphCount = font.textToGlyphs(current, preHyphenGlyphCount, SkTextEncoding::kUTF8, glyphs.data(), glyphs.size());

        // Draw pre-hyphen segment
        if (glyphCount > 0) 
        {
            // Allocate the run buffer
            const SkTextBlobBuilder::RunBuffer& buffer = builder.allocRun(font, glyphCount, currentX, y);
            // Copy the glyph indexes
            memcpy(buffer.glyphs, glyphs.data(), glyphCount * sizeof(SkGlyphID));
            // Advance the x coordinate inside the blob
            currentX += font.measureText(current, preHyphenGlyphCount, SkTextEncoding::kUTF8);
        }


        // Draw the soft-hyphen as a regular hyphen
        {
            // Convert hyphen into glyph index
            glyphCount = font.textToGlyphs("-", 1, SkTextEncoding::kUTF8, glyphs.data(), 1);
            // Allocate the run buffer for the hyphen
            const SkTextBlobBuilder::RunBuffer& buffer = builder.allocRun(font, glyphCount, currentX, y);
            // Copy the glyph index for the hyphen
            memcpy(buffer.glyphs, glyphs.data(), glyphCount * sizeof(SkGlyphID));
            // Advance the x coordinate by one
            currentX += font.measureText("-", 1, SkTextEncoding::kUTF8);
        }

        // Move to the next character after the soft hyphen
        current = end + 1;
    }

    // Draw the text blob
    sk_sp<SkTextBlob> blob = builder.make();
    canvas->drawTextBlob(blob, 0, 0, paint);
}

static void DrawString(SkCanvas* canvas, const SkFont* font, const SkPaint* paint, const char* string, SkScalar x, SkScalar y) 
{
    //canvas->drawString(string, x, y, *font, *paint);
    drawTextWithSoftHyphen(canvas, string, x, y, *paint, *font);
}

static void DrawEverything(SkCanvas* canvas, const char** texts, size_t textCount) 
{
    const auto timesTypeface = ToolUtils::CreateTestTypeface("Times", SkFontStyle{});
    const auto georgiaTypeface = ToolUtils::CreateTestTypeface("Georgia", SkFontStyle{});
    constexpr SkScalar fontHeight = 30.0f;
    constexpr SkScalar fontStartX = 10.0f;
    constexpr SkScalar fontStartY = 50.0f;
    SkFont timesFont(timesTypeface, fontHeight);
    SkFont georgiaFont(georgiaTypeface, fontHeight);

    SkPaint paint;
    paint.setAntiAlias(true);
    paint.setColor(SkColorSetARGB(0xff, 0xdd, 0x12, 0xaa));
    paint.setStyle(SkPaint::kFill_Style);

    for (size_t i = 0; i < textCount; ++i) 
        DrawString(canvas, &timesFont, &paint, texts[i], fontStartX, fontStartY + fontHeight * i);

    return;

    const char* text = MaxStr(texts, textCount);
    SkScalar xOffset = timesFont.measureText(text, strlen(text), SkTextEncoding::kUTF8);

    // Add a gap for the next text column
    xOffset += fontStartX;

    paint.setColor(SkColorSetARGB(0xff, 0xaa, 0x66, 0xbb));

    for (size_t i = 0; i < textCount; ++i) 
        DrawString(canvas, &georgiaFont, &paint, texts[i], xOffset, fontStartY + fontHeight * i);

    text = MaxStr(texts, textCount);
    xOffset = georgiaFont.measureText(text, strlen(text), SkTextEncoding::kUTF8);
}

int main(int argc, char** argv) 
{
    FiberData data = {};
    data.mainFiber = ConvertThreadToFiber(0);
    data.msgFiber = CreateFiber(0, (PFIBER_START_ROUTINE)FiberMessageProc, &data);

    if (!data.mainFiber || !data.msgFiber) return -1;

    sk_sp<skia::textlayout::FontCollection> fontCollection = sk_make_sp<skia::textlayout::FontCollection>();
    fontCollection->setDefaultFontManager(ToolUtils::TestFontMgr());
    skia::textlayout::ParagraphStyle style{};
    style.setReplaceTabCharacters(true);
    auto paraBuilder = skia::textlayout::ParagraphBuilderImpl::make(style, fontCollection);

    const char* texts[] = {"Softtttttttttttttttttttttttttttttttttttttttt\u00ADHyphen"};
    //texts[4] = (char)194;
    //texts[5] = (char)173;
    //const char* texts[] = {"biggg123456789111"};
    //const char* texts[] = {"Hello, World!!!"};
    //const char* texts[] = {"Bigasspaska.", "Hello.", "World."};
    //const char* texts[] = {"Bigasspaska."};

    for (size_t i = 0; i < ArrayCount(texts); ++i) 
        paraBuilder->addText(texts[i]);

    auto built = paraBuilder->Build();
    skia::textlayout::ParagraphImpl* paragraph = reinterpret_cast<skia::textlayout::ParagraphImpl*>(built.get());

    constexpr int w = 850, h = 600;
    RECT windowRectangle = {0, 0, w, h};

    AdjustWindowRectEx(&windowRectangle, WS_OVERLAPPEDWINDOW, FALSE, WS_EX_APPWINDOW);
    const HWND window = MakeWindow(windowRectangle.right - windowRectangle.left, windowRectangle.bottom - windowRectangle.top);

    data.window = window;

    if (ShowWindow(window, SW_SHOW)) return -1;

    SetWindowLongPtr(window, GWLP_USERDATA, (LONG_PTR)&data);

    MSG msg;
    memset(&msg, 0, sizeof(msg));
    while (!data.isQuit) 
    {
		PullFiberState(&data);

        const Area winArea = GetClientWindowArea(window);

        auto canvas = ResizeFrameBuffer(winArea.width, winArea.height);
        if (!canvas) continue;

        ClearFrameBuffers(canvas.get(), SkColors::kLtGray);

        paragraph->layout(winArea.width);
        paragraph->paint(canvas.get(), 0, 0);

        //DrawEverything(canvas.get(), texts, ArrayCount(texts));

        SwapFrameBuffers(window);

        PushFiberState(&data);
    }

    return 0;
}

#else

#endif // SK_ENABLE_SVG
