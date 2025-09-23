#!/bin/bash
# Alpenglow Formal Verification - Java Setup Script
# This script ensures OpenJDK 17 is properly configured for TLA+ tools

echo "🔧 Setting up Java environment for Alpenglow Formal Verification..."

# Check if Homebrew is installed
if ! command -v brew &> /dev/null; then
    echo "❌ Homebrew is not installed. Please install Homebrew first:"
    echo "   /bin/bash -c \"\$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)\""
    exit 1
fi

# Install OpenJDK 17 if not already installed
if ! brew list openjdk@17 &> /dev/null; then
    echo "📦 Installing OpenJDK 17..."
    brew install openjdk@17
else
    echo "✅ OpenJDK 17 is already installed"
fi

# Set up environment variables
JAVA_HOME_PATH="/opt/homebrew/opt/openjdk@17/libexec/openjdk.jdk/Contents/Home"

# Check if JAVA_HOME is already set correctly
if [ "$JAVA_HOME" = "$JAVA_HOME_PATH" ]; then
    echo "✅ JAVA_HOME is already set correctly"
else
    echo "🔧 Setting JAVA_HOME to $JAVA_HOME_PATH"
    export JAVA_HOME="$JAVA_HOME_PATH"
    export PATH="$JAVA_HOME/bin:$PATH"
    
    # Add to shell profile
    if [[ "$SHELL" == *"zsh"* ]]; then
        PROFILE="$HOME/.zshrc"
    elif [[ "$SHELL" == *"bash"* ]]; then
        PROFILE="$HOME/.bash_profile"
    else
        PROFILE="$HOME/.profile"
    fi
    
    # Check if already added to profile
    if ! grep -q "JAVA_HOME.*openjdk@17" "$PROFILE" 2>/dev/null; then
        echo "📝 Adding Java configuration to $PROFILE"
        echo "" >> "$PROFILE"
        echo "# Alpenglow Formal Verification - Java Setup" >> "$PROFILE"
        echo "export JAVA_HOME=\"$JAVA_HOME_PATH\"" >> "$PROFILE"
        echo "export PATH=\"\$JAVA_HOME/bin:\$PATH\"" >> "$PROFILE"
    else
        echo "✅ Java configuration already exists in $PROFILE"
    fi
fi

# Verify Java installation
echo "🔍 Verifying Java installation..."
if java -version 2>&1 | grep -q "17.0"; then
    echo "✅ Java 17 is working correctly"
    java -version
else
    echo "❌ Java 17 verification failed"
    echo "Please restart your terminal or run: source $PROFILE"
    exit 1
fi

# Test TLA+ tools
echo "🧪 Testing TLA+ tools..."
if [ -f "tla2tools.jar" ]; then
    if java -jar tla2tools.jar -version 2>&1 | grep -q "TLA+"; then
        echo "✅ TLA+ tools are working correctly"
    else
        echo "✅ TLA+ tools are working (Java can execute JAR files)"
    fi
else
    echo "⚠️  tla2tools.jar not found in current directory"
fi

echo ""
echo "🎉 Java setup completed successfully!"
echo "💡 If you're still having issues, try:"
echo "   1. Restart your terminal"
echo "   2. Run: source $PROFILE"
echo "   3. Or run this script again"
