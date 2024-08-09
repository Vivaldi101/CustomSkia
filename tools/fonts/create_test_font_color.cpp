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
#include "modules/skparagraph/src/ParagraphImpl.h"
#include "modules/skparagraph/include/Paragraph.h"
#include "modules/skparagraph/src/Run.h"
#include "modules/skparagraph/src/TextWrapper.h"
#include "modules/skparagraph/src/ParagraphImpl.h"
#include "modules/skparagraph/include/FontCollection.h"
#include "modules/skparagraph/include/ParagraphStyle.h"
#include "modules/skparagraph/include/Paragraph.h"
#include "modules/skparagraph/include/TextStyle.h"
#include <cmath>
#include <cassert>
#include <vector>
#include <algorithm>

#include <Windows.h>
#include <timeapi.h>

#pragma comment(lib, "skparagraph")
#pragma comment(lib, "winmm")

typedef size_t usize;
void DebugMessage(const char* format, ...);

#define ArrayCount(a) sizeof((a)) / sizeof(*(a))

#define Halt __debugbreak();
#define MAX_UPS (120)
#define MSEC_PER_SIM (1000 / MAX_UPS)

#define Pre(a) \
    if (!(a)) Halt
#define Post(a) \
    if (!(a)) Halt
#define Invariant(a) \
    if (!(a)) Halt

#define Implies(a, b) (!(a) || (b))
#define Iff(a, b) ((a) == (b))

#define ForI(b, n) for(u32 i = (b); i < (n); ++i)
#define ForJ(b, n) for(u32 j = (b); j < (n); ++j)
#define ForK(b, n) for(u32 k = (b); k < (n); ++k)

#define EQ(n, p) [&]() -> bool {for(usize i__ = 0u; i__ < (n); ++i__) { if ((p)) { return true; } } return false; }()
#define UQ(n, p) [&]() -> bool {for(usize i__ = 0u; i__ < (n); ++i__) { if (!(p)) { return false; } } return true; }()
#define UQI(i, n, p) [&]() -> bool {for(usize i__ = (i); i__ < (n); ++i__) { if (!(p)) { return false; } } return true; }()
#define CQ(n, p) [&]() -> usize {usize counter = 0; for(usize i__ = 0u; i__ < (n); ++i__) { if ((p)) { ++counter; } } return counter; }()

namespace
{
    constexpr size_t EmptyIndex = skia::textlayout::EMPTY_INDEX;
    // Maybe we can just use the unicode symbols to find?
    // TODO: Use std::arrays for these
    constexpr uint8_t softHyphen[2] = {0xC2, 0xAD};
    constexpr uint8_t hardHyphen[3] = {0xE2, 0x80, 0x90};

    // TODO: wp-semantics
    bool IsCharSoftHyphen(const std::string& text, size_t i) {
        return (uint8_t)text[i] == softHyphen[0] && (uint8_t)text[i+1] == softHyphen[1];
    };
    // TODO: wp-semantics
    bool IsCharHardHyphen(const std::string& text, size_t i) {
        return (uint8_t)text[i] == hardHyphen[0] && (uint8_t)text[i+1] == hardHyphen[1] && (uint8_t)text[i+2] == hardHyphen[2];
    };

    // TODO: Remove
    const auto IsAnyHardHyphen = [](const std::string& hyphenedText, size_t i)
    { return (uint8_t)hyphenedText[i] == hardHyphen[0] ||
        (uint8_t)hyphenedText[i] == hardHyphen[1] ||
        (uint8_t)hyphenedText[i] == hardHyphen[2]; };
    const auto IsAnySoftHyphen = [](const std::string& hyphenedText, size_t i)
    { return (uint8_t)hyphenedText[i] == softHyphen[0] ||
        (uint8_t)hyphenedText[i] == softHyphen[1]; };
}

    struct HyphenData
    {
        size_t hyphenIndex;
        bool isSoftHyphen;  // True if soft hyphen, false if hard
        bool isBreak;       // True if word break, false if not
    };

// Semantic compress the functions
// TODO: wp-semantics
// TODO: Use std::string functions where able
static size_t FindSoftHyphen(const char* utf8) 
{
    std::string utf8String{utf8};

    const auto result = utf8String.find(softHyphen[0]);
    if (result == utf8String.npos || (uint8_t)utf8String[result + 1] != softHyphen[1])
        return skia::textlayout::EMPTY_INDEX;

    return result;
}

// Semantic compress the functions
static size_t FindHardHyphen(const char* utf8) 
{
    std::string utf8String{utf8};

    const auto result = utf8String.find(hardHyphen[0]);
    if (result == utf8String.npos || (uint8_t)utf8String[result + 1] != hardHyphen[1] ||
        (uint8_t)utf8String[result + 2] != hardHyphen[2])
        return skia::textlayout::EMPTY_INDEX;

    return result;
}

static HyphenData FindSoftOrhardHyphen(const char* utf8) 
{
    HyphenData result = {};
    const auto soft = FindSoftHyphen(utf8);
    const auto hard = FindHardHyphen(utf8);

    result.isSoftHyphen = soft < hard;
    result.hyphenIndex = soft < hard ? soft : hard;

    return result;
}

// TODO: Pass in just the std string
// TODO: Harden indexing with wp-semantics
static std::string ReplaceExistingSoftHyphenWithHard(const char utf8[], size_t utf8Units, size_t shiftIndex) {
    Pre(IsCharSoftHyphen(utf8, shiftIndex));
    std::string utf8String{utf8};

    utf8String.resize(utf8String.size() + 1);

    memcpy(utf8String.data() + shiftIndex + 1, utf8 + shiftIndex, utf8Units - shiftIndex);
    memcpy(utf8String.data() + shiftIndex, hardHyphen, 3);

    return utf8String;
}

// TODO: Pass in just the std string
// TODO: Harden indexing with wp-semantics
static std::string ReplaceExistingHardHyphenWithSoft(const char utf8[], size_t utf8Units, size_t shiftIndex) {
    Pre(IsCharHardHyphen(utf8, shiftIndex));
    std::string utf8String{utf8};

    memcpy(utf8String.data() + shiftIndex, utf8 + shiftIndex + 1, utf8Units - shiftIndex - 1);
    memcpy(utf8String.data() + shiftIndex, softHyphen, 2);

    utf8String.erase(utf8String.end()-1);

    return utf8String;
}

static bool IsValidHyphenIndex(size_t index) {
    return index != skia::textlayout::EMPTY_INDEX;
}

static SkScalar GetTextPixelLength(const char* text, size_t textSize)
{
    const SkFont font = ToolUtils::DefaultFont();

    return font.measureText(text, textSize, SkTextEncoding::kUTF8);
}

static void FindAllSoftAndHardBreaks(skia::textlayout::ParagraphImpl* paragraphImpl, skia::textlayout::ParagraphBuilder* paraBuilder, std::vector<HyphenData>& hyphens, const std::string& text, const int layoutWidth) {
    const SkFont font = ToolUtils::DefaultFont();
    HyphenData data = {};
    const char* p = text.c_str();

    while (IsValidHyphenIndex((data = FindSoftOrhardHyphen(p)).hyphenIndex)) {
        const auto q = data.hyphenIndex;
        const auto preIndex = data.hyphenIndex + (p - text.c_str());
        const auto preBoundaryNumber = paragraphImpl->getLineNumberAt(preIndex);
        const auto postIndex = paragraphImpl->findNextSoftbreakBoundary(preIndex);
        const auto postBoundaryNumber = paragraphImpl->getLineNumberAt(postIndex);
        bool isBreak = (preBoundaryNumber != postBoundaryNumber);

        size_t lineBegin = 0;
        if (data.isSoftHyphen) {
            lineBegin = paragraphImpl->findPreviousSoftbreakBoundary(preIndex);
        }
        else {
            lineBegin = paragraphImpl->findPreviousSoftbreakBoundary(postIndex);
        }

        // post index returns as linebegin 

        #if 0
        if (isBreak && data.isSoftHyphen) {
            // Measure up to but not including the soft-hyphen
            SkScalar widthBefore = font.measureText(text.c_str() + beginIndex, data.hyphenIndex, SkTextEncoding::kUTF8);
            SkString hyphen("-");
            // Measure the hyphen
            SkScalar widthHyphen = font.measureText(hyphen.c_str(), hyphen.size(), SkTextEncoding::kUTF8);

            const float totalWidthWithHyphen = widthBefore + widthHyphen;

            isBreak = (totalWidthWithHyphen < layoutWidth);
        }
        else if (isBreak && !data.isSoftHyphen) {
            SkScalar widthBefore = font.measureText(text.c_str() + beginIndex, data.hyphenIndex+1, SkTextEncoding::kUTF8);
            isBreak = (widthBefore < layoutWidth);

            Post(widthBefore < layoutWidth);
        }
        #endif

        DebugMessage("Line begin index: %d\n", (int)lineBegin);

        //const auto textSize = GetTextPixelLength(text.c_str() + preIndex, postIndex - preIndex);

        data.isBreak = isBreak;
        data.hyphenIndex = preIndex;
        hyphens.push_back(data);

        const size_t offset = data.isSoftHyphen ? ArrayCount(softHyphen) : ArrayCount(hardHyphen);

        p += (q + offset);
    }

    Post(UQ(hyphens.size(), IsCharSoftHyphen(text, hyphens[i__].hyphenIndex) ^ IsCharHardHyphen(text, hyphens[i__].hyphenIndex)));
}

static std::string ConvertSoftBreaks(std::vector<HyphenData>& hyphens, const std::string& text) {
    std::string converted = text;
    for (size_t i = 0; i < hyphens.size(); ++i) {
        const auto isSoftHyphen = hyphens[i].isSoftHyphen;
        const auto isBreak = hyphens[i].isBreak;
        const auto hyphenIndex = hyphens[i].hyphenIndex;

        if (isSoftHyphen && isBreak) {
            const auto originalHyphens = hyphens;
            converted = ReplaceExistingSoftHyphenWithHard(converted.c_str(), converted.size(), hyphenIndex);
            // Shift every following index by one so that the hard-hyphen fits in
            for (size_t j = i + 1; j < hyphens.size(); ++j) {
                ++hyphens[j].hyphenIndex;
            }
            hyphens[i].isSoftHyphen = false;

            Post(Iff(isSoftHyphen && isBreak, UQI(i + 1, hyphens.size(), hyphens[i__].hyphenIndex == originalHyphens[i__].hyphenIndex + 1)));
        }
        if (!isSoftHyphen && !isBreak) {
            const auto originalHyphens = hyphens;
            converted = ReplaceExistingHardHyphenWithSoft(converted.c_str(), converted.size(), hyphenIndex);
            // Sync every index again
            for (size_t j = i + 1; j < hyphens.size(); ++j) {
                --hyphens[j].hyphenIndex;
            }

            hyphens[i].isSoftHyphen = true;

            Post(Iff(!isSoftHyphen && !isBreak, UQI(i + 1, hyphens.size(), hyphens[i__].hyphenIndex == originalHyphens[i__].hyphenIndex - 1)));
        }

        Post(Iff(!hyphens[i].isSoftHyphen && isBreak, IsCharHardHyphen(converted, hyphenIndex)));
        Post(Iff(hyphens[i].isSoftHyphen && !isBreak, IsCharSoftHyphen(converted, hyphenIndex)));

        Post(Iff(!hyphens[i].isSoftHyphen && isBreak, IsCharHardHyphen(converted, hyphenIndex)));
        Post(Iff(hyphens[i].isSoftHyphen && !isBreak, IsCharSoftHyphen(converted, hyphenIndex)));
    }

    return converted;
}

void DebugMessage(const char* format, ...) 
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

static int Sys_GetMilliseconds() {
	static DWORD sys_time_base = timeGetTime();
	return timeGetTime() - sys_time_base;
}

static int Com_ModifyFrameMsec(int frame_msec) {
	int clamped_msec = (int)(MSEC_PER_SIM + MSEC_PER_SIM);
	if (frame_msec > clamped_msec) {
		frame_msec = clamped_msec;
	}

	return frame_msec;
}

static float global_game_time_residual;
static int global_game_frame;

static int WaitForFrame() 
{
	int num_frames_to_run = 0;

	for (;;) {
		const int current_frame_time = Sys_GetMilliseconds();
		static int last_frame_time = current_frame_time;	
		int delta_milli_seconds = current_frame_time - last_frame_time;
		last_frame_time = current_frame_time;

		delta_milli_seconds = Com_ModifyFrameMsec(delta_milli_seconds);

		global_game_time_residual += delta_milli_seconds;

		for (;;) {
			// how much to wait before running the next frame
			if (global_game_time_residual < MSEC_PER_SIM) {		
				break;
			}
			global_game_time_residual -= MSEC_PER_SIM;
			global_game_frame++;
			num_frames_to_run++;
		}

		if (num_frames_to_run > 0) {
			// run the frames
			break;
		}
		Sleep(0);
	}

    return num_frames_to_run;
}


int main(int argc, char** argv) 
{
	timeBeginPeriod(1);
    FiberData data = {};
    data.mainFiber = ConvertThreadToFiber(0);
    data.msgFiber = CreateFiber(0, (PFIBER_START_ROUTINE)FiberMessageProc, &data);

    if (!data.mainFiber || !data.msgFiber) return -1;

    sk_sp<skia::textlayout::FontCollection> fontCollection = sk_make_sp<skia::textlayout::FontCollection>();
    fontCollection->setDefaultFontManager(ToolUtils::TestFontMgr());

    // Add hyphening into paragraphstyle?
    skia::textlayout::ParagraphStyle style{};
    style.setReplaceTabCharacters(true);
    auto paraBuilder = skia::textlayout::ParagraphBuilderImpl::make(style, fontCollection);

    //const char* texts[] = {"Soft\u00ADaa"};
    //const char* texts[] = {"FirstWord  fooooooooooooooooooo\u00ADtttt asdfoooooooooo bar Hyphen."};
    //const char* texts[] = {"Thisis aaaaaaaaaSoftttttttttttttttttttttttttttttttttttttttttttttt asd\u00ADa"};
    //const char* texts[] = {"--"};
    //const char* texts[] = {"Softttttttttttttttttttttttttttttttt tttttttttttttttttttttttttttttttt noHyphen."};

    const char* texts[] = {"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\u00ADcccccccccccccccccccccccccccccc\u00ADaaaaaaaaaaaaa"};
    //const char* texts[] = { "cccccccccc\u00ADyyyyyyyyyy" };
    //const char* texts[] = { "-" };

    //const char* texts[] = { "Lorem ip\u00ADsum do\u00ADlor sit amet, con\u00ADsecte\u00ADtur adip\u00ADisc\u00ADing elit. Etiam sed tris\u00ADtique pu\u00ADrus. Sed non cur\u00ADsus tel\u00ADlus. Fusce sus\u00ADcipit blandit viver\u00ADra. Cras non sagit\u00ADtis ur\u00ADna. Donec ali\u00ADquet ve\u00ADne\u00ADnatis odio, et eu\u00ADis\u00ADmod nunc eleifend feu\u00ADgiat. Proin vo\u00ADlut\u00ADpat lec\u00ADtus non eges\u00ADtas tin\u00ADcidunt. Sus\u00ADpendisse tin\u00ADcidunt eges\u00ADtas laoreet. Nunc et sapien con\u00ADse\u00ADquat, vestibu\u00ADlum eros sit amet, blandit sapi\u00ADen. Sus\u00ADpendisse a im\u00ADperdiet elit. Nam ornare vi\u00ADtae nulla sit amet ef\u00ADfici\u00ADtur. Donec ia\u00ADc\u00ADulis au\u00ADgue sit amet nibh mo\u00ADlestie dapibus." };

    constexpr int w = 500, h = 600;
    RECT windowRectangle = {0, 0, w, h};

    AdjustWindowRectEx(&windowRectangle, WS_OVERLAPPEDWINDOW, FALSE, WS_EX_APPWINDOW);
    const HWND window = MakeWindow(windowRectangle.right - windowRectangle.left, windowRectangle.bottom - windowRectangle.top);

    data.window = window;

    if (ShowWindow(window, SW_SHOW)) return -1;

    SetWindowLongPtr(window, GWLP_USERDATA, (LONG_PTR)&data);


    const std::string text = texts[0];
    std::string previousText = text;
    #if 0
    // TODO: wp-semantics
    auto Layout = [&paraBuilder, &text, &previousText](SkCanvas* canvas, int w, int h) {
        paraBuilder->Reset();
        paraBuilder->addText(previousText.c_str(), previousText.size());

        auto paragraph = paraBuilder->Build();
        paragraph->layout(w);
        const auto paragraphImpl = (skia::textlayout::ParagraphImpl*)(paragraph.get());

        std::vector<HyphenData> hyphens = {};

        FindAllSoftAndHardBreaks(paragraphImpl, paraBuilder.get(), hyphens, previousText, w);

        const std::string hyphenedText = ConvertSoftBreaks(hyphens, previousText);

        previousText = hyphenedText;

        paraBuilder->Reset();
        paraBuilder->addText(hyphenedText.c_str(), hyphenedText.size());
        paragraph = paraBuilder->Build();
        paragraph->layout(w);

        paragraph->paint(canvas, 0, 0);
    };
    #else
    paraBuilder->addText(text.c_str());
    auto Layout = [&paraBuilder, &text](SkCanvas* canvas, int w, int h) {
        auto paragraph = paraBuilder->Build();
        paragraph->layout(w);
        paragraph->paint(canvas, 0, 0);
    };
    #endif

    MSG msg;
    memset(&msg, 0, sizeof(msg));
    while (!data.isQuit) 
    {
		PullFiberState(&data);

        const Area winArea = GetClientWindowArea(window);

        auto canvas = ResizeFrameBuffer(winArea.width, winArea.height);

        if (!canvas) continue;

        ClearFrameBuffers(canvas.get(), SkColors::kDkGray);

        Layout(canvas.get(), winArea.width, winArea.height);

        const int framesToRun = WaitForFrame();

        SwapFrameBuffers(window);

        PushFiberState(&data);
    }

	timeEndPeriod(1);

    return 0;
}


//s sfd sfds
